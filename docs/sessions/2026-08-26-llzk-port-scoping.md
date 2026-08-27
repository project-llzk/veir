# LLZK → VEIR: scoping session, 2026-08-26

Working notes from a scoping session. Goal: verify LLZK's transformation
passes in VEIR. This records findings, decisions, and the next concrete step.

Everything below was verified by inspection on 2026-08-26 against
VEIR `46ee882cd` and `../llzk-lib` at the then-current worktree.

---

## 1. Repo state (verify before trusting anything else)

- HEAD `46ee882cd` "Merge opencompl/veir main into the LLZK fork", authored
  2026-08-26 10:26. Working tree clean.
- The merge migrated **nine LLZK dialects** out of the old monolithic
  `Veir/OpCode.lean` (which declared `Felt`, `Ram`, `Cast`, `Constrain`, … inline)
  into upstream's new per-dialect layout `Veir/Dialects/LLZK/<D>/OpInfo.lean` +
  `#generate_op_codes`.
- The migration happened during conflict resolution, so it is invisible to
  `git log <path>` (only the merge commit shows) and is bundled with ~822
  upstream files.
- Toolchain bumped **v4.31.0-rc2 → v4.33.0**.

**The tree DOES build.** A full build ran 10:06–10:24 on 2026-08-26, just before
the 10:26 commit, on the same (then-clean) working tree. All four binaries
produced: `run-benchmarks` 10:11, `veir2mir`/`veir-interpret` 10:14, `veir-opt`
10:16; `UnitTest.olean` 10:24. Olean counts: LLZK dialects 15, Passes 34,
Rewriter 40, Interpreter 8, UnitTest 29.

Critically, **the Felt proof surface compiled**: `Passes/Felt/Proofs.olean`
10:11 and `Passes/Felt/RewriteLemmas.olean` 10:15 (the 1,012 lines of sorry-free
rewrite proofs). FOLLOWUP.md warned that upstream's Rewriter/WfRewriter/
WellFormed refactor could invalidate those — it did not.

**But compiling is not the same as proved.** `sorry` yields an olean with only a
warning; `partial def` bodies are never kernel-checked; `#eval!` permits terms
the kernel would reject. So the checks that actually matter next session are:

```bash
uv run lit Test/LLZK/ -v      # outside lake, leaves no oleans, exercises round-trip + passes
```
plus `#print axioms` on the Felt proof surface, looking for `sorryAx` and
`WfIRContext.Dom` (`Veir/Dominance.lean` still declares 18 axioms).

Note the `isIsolatedFromAbove` gap below compiles fine and always will — it is a
missing trait, not a type error, so no build will surface it.

### Bug found during the migration audit

`Veir/Dialects/LLZK/Function/OpInfo.lean` does **not** set
`isIsolatedFromAbove`, so it falls back to the `HasOpInfo` default of `false`.
But LLZK's `FuncDefOp` carries `IsolatedFromAbove` in TableGen and documents it
("functions are `IsolatedFromAbove`"). Upstream's own `Func` dialect *does* set it.

Consequences: (1) VEIR accepts function bodies capturing outer values that LLZK
rejects; (2) `RegionPtr.nearestIsolatedScope?` walks past `function.def`, and
`Veir/Passes/CSE.lean` puts that scope in its dedup `Key` — so `veir-opt -p=cse`
on LLZK IR could rewire a use across a function boundary. That is a miscompile.

Fix:
```lean
def Function_.isIsolatedFromAbove (op : Function_) : Bool :=
  match op with | .«def» => true | .return => false
```
plus the field in the `HasOpInfo` instance.

Root cause worth remembering: `hasSSADominance` has **no default** in
`HasOpInfo`, so migration was forced to write it for every dialect;
`isIsolatedFromAbove` **has** a default, so it silently defaulted. Audit the
other defaulted fields (`getRegionKind`, `hasNoTerminator`, `propagatesPoison`)
the same way — they matter when Struct lands.

### FOLLOWUP.md is now stale in three places

- `Veir/Dominance/Basic.lean` is new: 247 lines, real CompCertSSA-style
  definitions, **0 axioms**. (`Veir/Dominance.lean` still declares 18 axioms and
  now imports Basic — upstream is mid-migration.)
- `Veir/PatternRewriter/Semantics.lean` now defines
  `LocalRewritePattern.PreservesSemantics` and `LocalRewritePattern.Sound`
  (upstream #747), plus `InterpreterState.isRefinedBy` generalization (#765) and
  new `Interpreter/Refinement/Monotonicity.lean`, `Interpreter/Evaluate.lean`.
  This is the interpreter-simulation framework the F2 memo said did not exist.
- `Veir/Rewriter/GetSet/DetachOp.lean` (845 lines) and `CreateOp.lean` /
  `InsertOp.lean` have **0 sorries**, with 24 proven `_eraseOp` lemmas and a full
  `_createOp` complement.

**The F2 GO/NO-GO on the whole-program keystone was decided against a tree that
no longer exists. Re-run it.**

Current axiom inventory: 18 in `Dominance.lean`, **4 in
`Interpreter/Lemmas.lean`** (`interpretOp'_ne_fail`, `_monotone`,
`_results_conform`, `_branch_dest_mem` — these bite anyone doing
interpreter-based semantics), 1 `Verifier.lean`, 2 `ForLean.lean`, 1
float-bits axiom in `Attribute.lean`.

---

## 2. What LLZK actually looks like (measured, not assumed)

### The subset boundary already exists in LLZK

`include/llzk/Dialect/Function/IR/OpTraits.td` defines three traits enforced by
function attributes:

| trait | gate | meaning |
|---|---|---|
| `WitnessGen` | `function.allow_witness` | only in `@compute` |
| `ConstraintGen` | `function.allow_constraint` | only in `@constrain` |
| `NotFieldNative` | `function.allow_non_native_field_ops` | "must be rewritten or folded into a constant after the flattening and unrolling pass" |

Felt splits 6 / 12:
- **field-native**: `const, add, sub, mul, div, neg`
- **non-native**: `pow, uintdiv, sintdiv, umod, smod, inv, bit_and, bit_or,
  bit_xor, bit_not, shl, shr`

(Asymmetry worth asking Veridise about: `div` is native but `inv` is not, even
though div is defined as multiply-by-inverse.)

The compute/constrain split is enforced by *attribute*, not convention — so
`compute` denotes a **function** and `constrain` denotes a **predicate**, and the
type system keeps them apart for you.

### The production corpus: `~/veridise/llzk-benchmarks/plonky3/sp1-hypercube`

47 files, 193 MB of real SP1 circuits.

| op | count | | op | count |
|---|---|---|---|---|
| `felt.add` | 216,583 | | `cast.tofelt` | 20,831 |
| `felt.mul` | 201,129 | | `bool.cmp` | 20,831 |
| `felt.sub` | 44,989 | | `global.read` | 319 |
| `constrain.eq` | 42,524 | | `constrain.in` | 319 |
| `struct.field` | 23,409 | | `array.new` | 316 |
| `struct.readf` | 22,598 | | `function.def` | 162 |
| `felt.const` | 2,254 | | `struct.new` / `def` | 81 |
| `felt.neg` | 1,099 | | `global.def` | 27 |

**Zero** occurrences of: any non-native felt op, `array.read`, `array.write`,
`function.call`, `struct.writef`, `scf.*`, `poly.*`.

Structural facts that follow:
1. **`compute` is empty.** Zero `struct.writef`; compute bodies are 1–8 ops,
   almost all just `struct.new; return`. Struct fields are trace columns — free
   existential variables. All content is in `constrain`.
2. **Arrays are never indexed.** `array.new` (316) pairs 1:1 with `constrain.in`
   (319) and `global.read` (319) — lookup-argument tuples against a constant
   table, never a data structure.
3. **The only non-native ops are range checks.** All 20,831 `bool.cmp` are `lt`,
   each feeding a `cast.tofelt` constrained to 1, against a constant power of two.
4. **100% bare `!felt.type`** — 6,508,937 bare, zero named, zero `llzk.fields`.
   Module attribute is the *older* `veridise.lang = "llzk"`.

Contrast the Circom-derived tests (`llzk-lib/test/FrontendLang/Circom`):
`array.read` 58, `struct.writem` 30, `function.call` 27, `scf.for` 18,
`poly.template` 20, `poly.param` 19, `llzk.nondet` 9. **Two different
sublanguages.** Your target corpus decides which you sign up for.

### What LLZK's felt folder actually does

`lib/Dialect/Felt/IR/Ops.cpp`: `tryGetBinaryFoldData` bails unless **both**
operands have field names that are non-null, equal, and registered. And
`buildFoldResult` constructs the result APInt at `field.bitWidth()`, so with no
field there's no width to target — that is the real reason for the guard, not
unsoundness.

Consequence: **on the SP1 corpus, LLZK's felt folder is completely inert.**

But the bigger finding: felt ops declare `hasFolder = 1` and **no
`hasCanonicalizer`**; there are zero `matchAndRewrite` definitions in Ops.cpp.
**LLZK has no algebraic simplification for felt at all, at any field.**

Measured on SP1:

| pattern | sites |
|---|---|
| `add x, 0 → x` | 16,425 |
| `mul x, 1 → x` | 9,654 |
| `mul x, 0 → 0` | 2,455 |
| `sub x, 0 → x` | 617 |
| **total** | **29,151** (~6.3% of all felt binops) |

vs. only **48** foldable constant pairs out of 462,701 binops (0.01%).

So: C++ isn't missing constant folding in any way that matters. It's missing
algebraic simplification entirely — and VEIR already has 15 sorry-free patterns
covering it. (Static syntactic counts from regex over pre-optimization IR;
order-of-magnitude, not a benchmark.)

**This kills the "C++-parity profile" as a goal.** Matching a pass that does
nothing means suppressing your own verified optimizer. Repurpose the differential
harness from "must match" to "must not disagree on anything C++ actually rewrites."

### Felt fields: the prime is not in the type

`!felt.type` carries an optional *name* only (`OptionalParameter<StringAttr>`).
The prime lives in `LLZK_FieldSpecAttr` on the root module:
```
module attributes {llzk.lang, llzk.fields = field<foo, 7>} { ... }
```
Built-ins (`bn128`/`bn254`, `grumpkin`, `babybear`, `goldilocks`, `mersenne31`,
`koalabear`) are hardcoded in `Util/Field.cpp::initKnownFields`.
`Veir/Passes/Felt/InterpModel.lean`'s `feltPrime` matches all seven exactly, but
is a pure function of the name — it cannot see `llzk.fields`, so a user-declared
field silently resolves to `none` in VEIR and to its prime in LLZK.

**But this is off the critical path.** `const` is `Int.cast : ℤ → ZMod p`, a ring
hom, so `const a ⊕ const b = const (a ⊕ b)` holds in *every* `ZMod p`. Folding is
modulus-independent; only *reducing the literal into [0,p)* needs `p`, and that
is representational, not semantic.

`Field::reduce` = `i % p`, `+p` if negative. `Field::toSigned` =
`i < (p+1)/2 ? i : i - p`. `inv` = `modInversePrime`. Mirror those when the
non-native ops eventually matter.

Also: `typesUnify` (`lib/Util/TypeHelper.cpp:720`) has **no `FeltType` case** —
it succeeds only on `lhs == rhs` or a `TypeVarType`. So **same-field on binary
ops is statically enforced**, and a multi-field module decomposes into
independent single-field circuits. `FieldEnv` is consumed once at denotation
time; `Sat` stays `{p}`-parameterized and theorems are `∀ p`.

Known C++ bug: `Field::addField` guards on *existence*, not prime mismatch, so
re-declaring `field<foo, 7>` with the same prime is a fatal error. Worth
reporting.

---

## 3. Architecture decisions reached

### VEIR is a closed world; that is the price of theorems

One `inductive Attribute` (~46 cases) holds every type/attribute; one `OpCode`
inductive holds every op, assembled by `#generate_op_codes` from per-dialect
imports in `Veir/OpCode.lean`. MLIR's open registry cannot be reasoned about
exhaustively — closedness buys decidable equality and total functions.

Costs, measured:
- **adding a dialect: one import line** (nothing else propagates; every
  exhaustive `OpCode` match has a catch-all)
- **adding a type: ~9 sites in 2 files** (`IR/Attribute.lean` ×6,
  `Parser/AttrParser.lean` ×3; printer needs nothing — it goes through `ToString`)
- **escape hatch**: `UnregisteredAttr` (`isType := true`) round-trips unknown
  types for free, and `builtin.unregistered` does the same for ops behind
  `--allow-unregistered-dialect`. **You only pay registration cost for what you
  reason about.**

### Three activities, not one "port"

1. **Transcription** (mechanical, ODS-automatable): opcodes, arity, traits.
2. **Reimplementation** (real, bounded): folders/canonicalizers → Lean patterns.
3. **Specification** (new construction): what does `felt.add` / `constrain.eq`
   *mean*? **MLIR has no semantics — the C++ `fold()` is the de facto spec.**
   There is nothing to port here; you are deciding it for the first time.

Semantics cost scales with **semantic domains** (felt arithmetic, constraint
systems, arrays), not with op count. Nine dialects ≠ 9× the work.

### ODS → OpInfo.lean generation is viable, verified working

```bash
llvm-tblgen --dump-json -I include -I /opt/homebrew/opt/llvm@20/include \
  include/llzk/Dialect/Felt/IR/Ops.td -o felt.json
```
(`mlir-tblgen`/`llvm-tblgen` are at `/opt/homebrew/opt/llvm@20/bin/`; tested,
597 KB of JSON, all 18 Felt mnemonics + arities + traits recovered correctly.)

Operand vs attribute is recoverable from `!superclasses`: `AttrConstraint` →
`propertiesOf`, `TypeConstraint` → operand. Derivable: opcode inductive,
`verifyPlainOpCounts n m`, properties fields, `Pure`→`getEffects := .none`,
`ConstantLike`, `Terminator`, `IsolatedFromAbove`, `NoTerminator`, and the
field-native subset filter. Not derivable: `hasVerifier` C++ bodies, variadic
segments, `extraClassDeclaration`, inlined `anonymous_NNN` `PredOpTrait`s.
~80% generated, hand-written tail per dialect.

**Make it offline codegen with a checked-in artifact + a CI regenerate-and-diff
job** — that diff is your only signal that LLZK's ODS drifted. Do *not* make it a
Lake build step (would make VEIR depend on LLZK's build tree).

### Decision: verify passes on the IR, not on a reified `Circuit`

Considered and rejected: `denote : IR → Circuit`, transform `Circuit`, re-emit.
`Circuit` is a **lossy view** (drops locations, discardable attrs, unmodeled ops);
regenerating IR from it means the theorem is about the regeneration, not the pass.
Passes stay on the IR via `PatternRewriter` (`createOp`/`eraseOp`/`replaceValue`),
which is also what keeps them composable (`-p felt-combine,dce`) and safe on
modules containing ops you have no semantics for.

So: define satisfaction **directly on the IR** (`IRSat`), fusing
`Sat ∘ denote`. One fewer datatype, no commuting lemma.

You still keep:
- **state monads** — VEIR passes are already written this way
  (`Veir/Passes/CSE.lean`: `Id.run do` + `let mut ctx` + `let mut available`).
  Degree lowering's state is literally the C++'s `DenseMap<Value,Value>& rewrites`
  + `SmallVector<AuxAssignment>&`. That correspondence is what makes the
  "structurally identical to the C++" story work.
- **semantic objects** — `Assignment p := Signal → ZMod p`, `ZMod p`, the value
  environment. Only the top-level `Circuit` *record* goes away.

`Circuit` may return in minimal form for degree lowering, which needs a handle on
"the signals the pass introduced" to write `∃τ`.

---

## 4. `IRSat` — the piece that does not exist

There is **no generic notion of satisfaction in VEIR, and there cannot be.**
VEIR's built-in semantics is entirely *operational* (`interpretOp'`,
`InterpreterState`, `isRefinedBy`, `PreservesSemantics`) — it fits dialects where
ops *compute*. `constrain.eq` has zero results; it *asserts*. LLZK's constrain
dialect is the first declarative dialect VEIR has ever had.

| | operational (built in) | declarative (write it) |
|---|---|---|
| per op | `Felt.interpretOp'` | `evalFeltOp` |
| whole body | `interpretOpList` → `InterpreterState` | `evalBody` → env + eqs |
| correctness | `isRefinedBy` / `PreservesSemantics` | `IRSat ctx' σ ↔ IRSat ctx σ` |
| exists? | yes | **no — ~40 lines you write** |

Sketch (`σ` assigns only to *free* variables — block args and `struct.readm`
results; everything else is computed):

```lean
abbrev ValEnv (p : Nat) := Std.HashMap ValuePtr (ZMod p)

def evalFeltOp (ctx) (op) (env : ValEnv p) : Option (ZMod p) :=
  match op.getOpType! ctx with
  | .felt .const => some ((op.getProperties! ctx _).value : ZMod p)   -- Int.cast
  | .felt .add   => do return (← env[ops[0]!]?) + (← env[ops[1]!]?)
  | .felt .sub | .felt .mul | .felt .neg => ...
  | _ => none

def satOfList (ctx) : List OperationPtr → ValEnv p → List (ZMod p × ZMod p) → Prop
```

Worked example at `p = 7` for `%0=mul %a %b; %1=const 3; %2=add %0 %1;
constrain.eq %2 %a`: with `σ a = 2, σ b = 3` → `env[%2] = 9 ≡ 2 = env[%a]`, holds.
With `σ a = 1, σ b = 1` → `4 ≠ 1`, fails.

### Define it over a LIST, never a linked-list walk

A `partial def` walking `next!` is opaque to the kernel — you cannot prove
anything about it, and there is no decreasing measure. Structural recursion on a
`List OperationPtr` is total and inducts trivially.

**VEIR already does exactly this**: `interpretOpChain` (walks, executable) vs
`interpretOpList` (list recursion, provable), bridged by
`interpretOpChain_eq_interpretTerminatedOpList_of_opChain`
(`Interpreter/Lemmas.lean:611,625`). Copy that shape.

### How to get the op list

`IRContext.WellFormed` has a field (`Veir/IR/WellFormed.lean:688`):
```lean
opChain (blockPtr) (blockPtrInBounds) : ∃ array, BlockPtr.OpChain blockPtr ctx array
```
`WfIRContext = { raw, wellFormed }`, so every well-formed context carries it.
`BlockPtr.OpChain_unique` makes the array canonical.

**It is `Prop`-valued** — you cannot eliminate it into `IO`/`Type` (large
elimination). It is proof-only machinery.

Ready-made noncomputable helpers (`WellFormed.lean:867, 889, 912`), both proof
args are `:= by grind` auto-params:
```lean
noncomputable def BlockPtr.operationList  (block) (ctx) ... : Array OperationPtr
noncomputable def RegionPtr.blockList     (region) (ctx) ... : Array BlockPtr
noncomputable def ValuePtr.defUseArray    (value) (ctx) ... : Array OpOperandPtr
```
with grind-tagged lemmas: `operationListWF`,
`@[grind =] operationList_iff_BlockPtr_OpChain`,
`@[grind =_] operationList.mem` (membership characterization — directly useful
for dedup), plus `blockList` mirrors.

**Two tracks, they never meet in one definition:**

| | executable (`inspect`, the pass) | proof (`IRSat`, theorems) |
|---|---|---|
| ops of a block | `partial def opsOf` (write it) | `BlockPtr.operationList` |
| blocks of a region | `partial def blocksOf` (write it) | `RegionPtr.blockList` |
| uses of a value | walk `firstUse`/`nextUse` | `ValuePtr.defUseArray` |

Gotcha hit in practice: `while let some o := cur do` with no
`cur := (o.get! c).next` spins forever, and `#eval!` runs *inside the language
server* with no timeout — it hangs the extension. Recovery: Cmd+Shift+P →
"Lean 4: Restart Server". Fix: write the advance once in a helper, use `for`
everywhere else.

---

## 5. The plan

### M1 — constraint dedup on the IR (next session)

`llzk-duplicate-op-elim`, the `constrain.eq` half. **Requires zero dialect
porting**: Felt (18 opcodes) and Constrain (`eq`) are both already registered.

Why this first:
- `constrain.eq` has **0 results** → `eraseOp`'s `!op.hasUses!` is free, and
  there is **no `replaceValue` at all** (the hard part of erasure is vacuous)
- **0 regions** → `getNumRegions! = 0` free
- erasing it **does not perturb `env`** (it defines nothing), so `IRSat` after =
  before minus one conjunct, implied by the surviving duplicate
- every accessor the proof needs has a proven `_eraseOp` lemma
  (`getOpType!`, `getProperties!`, `getOperands!`, `next!`, `firstOp!`,
  `getNumArguments!`, `getType!`). The lemmas still marked "missing because it is
  quite complex to state" are **all use-def chain internals** — `IRSat` walks
  forward and reads operands, never traversing use chains, so none block it.

Test input that parses in VEIR **today** (generic form only; felt const attr is
`#felt<const N> : !felt.type`):
```mlir
"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %0 = "felt.mul"(%a, %b) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%0, %a) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%0, %a) : (!felt.type, !felt.type) -> ()
}) : () -> ()
```
`Test/LLZK/Felt/passes/right_identity.mlir` is already this shape.

Work items:
1. `IRSat` / `satOfList` / `evalFeltOp` — over a list, `∀ p`
2. the pass — **not** a `LocalRewritePattern` (match depends on *earlier* ops);
   model on `Veir/Passes/CSE.lean`, a `HashSet (ValuePtr × ValuePtr)` of seen pairs
3. `theorem dedup_preserves_sat : satOfBlock ctx' b σ ↔ satOfBlock ctx b σ`
4. FileCheck test + differential vs `result/bin/llzk-opt --llzk-duplicate-op-elim`

Note `constrain.eq` has `getEffects := .write` *deliberately* ("it has no
results, so it must report an effect or DCE would erase the constraint system").
So CSE will not already do this (CSE only handles memory-independent ops), and
DCE will not delete constraints. Your pass erases on **semantic** grounds, not
liveness.

### M2 — degree lowering (`llzk-poly-lowering-pass`, 1,095 LoC C++)

Not pattern-based — an imperative walk with `DenseMap<Value,Value>& rewrites`,
`SmallVector<AuxAssignment>&`, a **topological sort** of aux assignments
(`orderAuxAssignments`, because `compute` writes must be dependency-ordered), and
degree checking. That is a state monad written by hand; the Lean port is a
`StateM` over `{rewrites, auxMembers, auxAssignments, nextAux}`.

**One `fresh` = three IR edits:** a `struct.member` declaration, a
`struct.writem` in `compute`, and a `struct.readm` + `constrain.eq` in
`constrain`. The last two are *precisely the two directions of the existential*.

Theorems (all four needed):
```lean
-- T1  equisatisfiability up to projection
∀ σ, IRSat ctx C σ ↔ ∃ τ : A → ZMod p, IRSat ctx' C' (σ ⊕ τ)

-- T1c  the ZK-critical strengthening: no new witness freedom
∀ σ, IRSat ctx C σ → ∃! τ, IRSat ctx' C' (σ ⊕ τ)

-- T2  functional correctness (pure syntax, no semantics — prove this FIRST)
∀ eq ∈ constraints(C'), max (deg lhs) (deg rhs) ≤ maxDegree
    where deg(signal)=1, deg(const)=0, deg(add/sub)=max, deg(neg)=id, deg(mul)=+

-- T3  compute preservation
∀ inp, (⟦compute'⟧ inp)|M = ⟦compute⟧ inp ∧ (⟦compute'⟧ inp)|A = τ₀ (⟦compute⟧ inp)
```

T1 alone is satisfied by the identity pass. T2 alone by a pass that deletes
everything. **You need both.** T1c is what rules out under-constraining (the #1
ZK bug class); its proof is induction on the topological order — which is exactly
why `orderAuxAssignments` exists.

`compute` is a **function** (`Inputs → Witness`, operational — fits VEIR's
existing interpreter once Felt is wired in), `constrain` is a **predicate**
(declarative — needs `IRSat`). M1 needs only the second.

### Soundness preservation — a corollary, not extra work

```lean
def Sound (C) : Prop :=
  (∀ inp, P (f inp) inp)                       -- completeness
∧ (∀ inp w, P w inp → w|pub = (f inp)|pub)     -- soundness
```
`Sound C → Sound C'` follows from T1a (constructive: `P σ → P' (σ ⊕ τ₀ σ)`),
T1b, T3, and **T4: `pub(S') = pub(S)`** — i.e. aux members must not be public.
(They aren't: the C++ emits `struct.member @__llzk_poly_lowering_pass_aux_member_0
: !felt.type` with no `{llzk.pub}`. Add it as a checked side condition.)

You verify the *pass* once and soundness transfers to **every circuit anyone runs
it on**, and composes across passes. That is the leverage of verifying compilers
rather than programs.

Scope note: `Sound` is soundness *relative to `compute`* — it does not say the
circuit computes the right thing. ZKLean/Picus/hand proofs establish that a given
circuit is correct; VEIR establishes the compiler does not destroy it. Neither
replaces the other; together they are end-to-end. (ZKLean —
`llzk-lib/backends/zklean`, 2,154 LoC, `ZKExpr` pure expressions + `ZKBuilder`
`ConstrainEq`/`AllocWitness` — is a pretty-printer with no semantics and no
pass-correctness story. `AllocWitness` is the same `fresh` operation.)

### M3 — the Struct dialect port

**Struct was never in VEIR** — not pre-merge (the monolithic `OpCode.lean` had 22
dialects, no Struct/Array), not now. Nothing was lost in the migration.

Needed when you want to run on real SP1 circuits (`struct.readf`) or do degree
lowering (which *adds* members):
1. `Veir/Dialects/LLZK/Struct/Properties.lean` — `StructDefProperties{symName}`,
   `MemberDefProperties{symName, type, column, signal}`,
   `MemberReadProperties{memberName}`, `MemberWriteProperties{memberName}`
2. `Veir/Dialects/LLZK/Struct/OpInfo.lean` — `def, member, new, readm, writem`;
   **`struct.def` needs `isIsolatedFromAbove := true`, `getRegionKind := .Graph`,
   `hasNoTerminator := true`** (LLZK gives it `GraphRegionNoTerminator.traits`)
3. `!struct.type` in `IR/Attribute.lean` (~6 sites)
4. parser case in `Parser/AttrParser.lean` (~3 sites)
5. one import line in `Veir/OpCode.lean`

Key design fact: **LLZK struct types are nominal, not structural.**
`!struct.type<@S<[...]>>` = symbol ref + optional params; the fields live as
`struct.member` ops inside the `struct.def` region. So the type case stays a flat
pair (mutual recursion between structs never touches the *representation*), but
typing `struct.readm` needs **symbol lookup**, which is non-local — VEIR's
`verifyLocalInvariants` can't do it, so it needs a module-level pass.
`Veir/IR/SymbolTable.lean` has `resolveFlatSymbol`/`resolveSymbol` but is thin
(131 lines).

`{signal}` marks witness variables ("stored in the witness; non-signal values are
intermediate expressions") — that is the semantic keystone for the constraint
denotation. It is a recent addition, which is why the older SP1 corpus has none
(treat all felt members there as signals).

Defer: `column`/`tableOffset` (needs `AffineMapAttr`, which **VEIR does not
have**), and template params — restrict to the closed fragment (no `SymbolRefAttr`
/ `AffineMapAttr` / `!poly.tvar` in any type) with a well-formedness predicate.
SP1 is `struct.def @X<[]>` throughout — 100% in the closed fragment.

**Do not model LLZK's type parameters with Lean's own type parameters.** VEIR's
IR is deeply embedded (`Attribute` is data that gets hashed, compared, parsed);
passes must *compute* on types (substitute, unify, destructure). Parametricity
must be syntax with binders.

### Layered subset, for reference

- **L0** flat field-native core (felt const/add/sub/mul/neg, constrain eq/in,
  monomorphic struct as signal namespace, function def/return, global def/read,
  array.new as tuple, + two fused primitives: `InRange` for range checks,
  `∃i, table[i] = tuple` for lookups). **Covers 100% of SP1.** Unlocks
  poly-lowering, duplicate-op-elim, redundant-read-write-elim, unused-decl-elim.
- **L1** `function.call`, struct-typed members → inline-structs
- **L2** indexed arrays, `scf.for` → array-to-scalar, while-to-for
- **L3** templates (`poly.*`, 7 ops, 9,004 LoC C++) → flatten. Most expensive by
  far; defer.

Pass selection rule: **port what needs only infrastructure you have; validate
what needs infrastructure you don't.** VEIR has DataFlowFramework, SideEffect,
ControlFlow, DataLayout interfaces. It lacks InliningUtils, CallGraph,
CallInterface, and MemorySlot/SROA/mem2reg (which `llzk-pod-to-scalar` needs).

---

## 6. Tooling state

- `~/veridise/llzk-lib/result/bin/llzk-opt` **works** — but it is the *old*
  dialect: `struct.field`/`struct.readf`, module attr `veridise.lang = "llzk"`.
  Verified: parses, round-trips, and `--llzk-duplicate-op-elim` correctly
  collapses two identical `constrain.eq` to one. **This is your M1 oracle.**
- `~/veridise/llzk-lib/build/bin/llzk-opt` is **broken** — missing
  `libLLVM.dylib` from a garbage-collected nix store path. Worth fixing before
  you need a *current*-dialect oracle for struct-level tests.
- `include/` sources are the **new** dialect (`struct.member`/`readm`,
  `llzk.lang`). Felt and constrain mnemonics are stable across both, so M1 is
  unaffected; struct-level differential testing will force a choice.
- `scripts/llzk-diff.sh` is textual diff + normalizer + per-test fixed-string
  allowlists, with `--lower-first` to run input through
  `llzk-opt --mlir-print-op-generic` (VEIR parses generic form only). Fine for
  peepholes; **will not survive poly-lowering** (aux member names and extraction
  order are traversal-dependent, so two correct implementations differ
  textually). That is the argument for translation validation over differential.
- `mlir-tblgen` / `llvm-tblgen` at `/opt/homebrew/opt/llvm@20/bin/`.
- Disk: **41 GB free** on the data volume (`df /` shows the read-only system
  volume — ignore it). `.lake` is 9.6 GB; Mathlib 8,322 oleans / 6.5 GB, Veir 278
  oleans / 2.1 GB, none newer than the merge.
- VS Code: `leanprover.lean4-0.0.239` installed, elan on PATH, v4.33.0 present.
  If the ∀ icon is missing: reload the window (the extension caches the toolchain
  and it changed under it), and confirm the workspace folder is
  `~/veridise/veir` itself, not the parent.

---

## 7. Open questions for Veridise

1. What is the precise rule for signal-ness when `{signal}` is absent? The
   `StructDefOp` docs say Main-component inputs are signals "even though they are
   not marked". Load-bearing for the constraint denotation.
2. Why is `felt.div` field-native but `felt.inv` not?
3. `Field::addField` rejects a re-declaration with the *same* prime (guards on
   existence, message implies mismatch). Bug?
4. Is the `struct.field` → `struct.member` migration final? Affects emitter
   target and the benchmark corpus.
