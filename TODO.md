# LLZK-in-VeIR: Implementation Plan

Goal: implement LLZK passes in VeIR as **real IR passes**, and prove them
semantics-preserving. The end state is a soundness-preservation theorem:
if a circuit was sound before the pass, it is sound after.

Not the goal: a standalone Lean model that re-emits MLIR. Passes operate on
`WfIRContext`, same as every other VeIR pass.

---

## Phase 0 — Verify the merge (do this first)

The merge `46ee882cd` migrated all nine LLZK dialects from the old monolithic
`Veir/OpCode.lean` into upstream's new per-dialect `Veir/Dialects/<D>/OpInfo.lean`
layout, during conflict resolution. It is invisible in history — `git log` on
those paths shows only the merge commit.

**The tree does build.** A full build ran 10:06–10:24 on 2026-08-26, just before
the 10:26 commit on the same clean tree: all four binaries, and crucially
`Passes/Felt/Proofs.olean` and `RewriteLemmas.olean` compiled — upstream's
Rewriter/WellFormed refactor did not break the Felt proofs. But compiling is not
proved: `sorry` yields an olean with only a warning, `partial def` bodies are
never kernel-checked, and `#eval!` permits kernel-rejected terms. So the checks
below still matter, and `lake build` is the least informative of them.

- [ ] `lake build`
- [ ] `lake test`
- [ ] `uv run lit Test/LLZK/ -v`
- [ ] If anything broke: check the migrated dialects against their pre-merge
      inline definitions with `git show 1be2f5da0:Veir/OpCode.lean`
      (dialect inductives) and `git show 1be2f5da0:Veir/Verifier.lean`
      (verification logic, e.g. `constrain.eq` at line 1138).
- [ ] Re-run `#print axioms` on the Felt proof surface. The F2 go/no-go in
      `FOLLOWUP.md` was decided against a tree that no longer exists —
      `Veir/Dominance/Basic.lean` is now a real formalization and
      `Veir/PatternRewriter/Semantics.lean` has `LocalRewritePattern.Sound`.

Space is tight on this machine; budget for the Mathlib cache.

---

## Phase 1 — `IRSat`: what an LLZK constrain body means

New file: `Veir/Dialects/LLZK/Semantics/Constraint.lean`

VeIR's built-in semantics is entirely **operational** (`interpretOp'`,
`InterpreterState`, `isRefinedBy`) — it models ops that *compute*.
`constrain.eq` has zero results; it *asserts*. There is no built-in notion of
satisfaction because LLZK's constrain dialect is the first declarative dialect
VeIR has had. This phase writes that notion.

- [ ] `abbrev Signal := Nat`, `abbrev Assignment (p : Nat) := Signal → ZMod p`
- [ ] `abbrev ValEnv (p : Nat) := Std.HashMap ValuePtr (ZMod p)`
- [ ] `evalFeltOp` — one case per field-native felt op
      (`const`, `add`, `sub`, `mul`, `neg`). `const` is `Int.cast : ℤ → ZMod p`,
      the ring hom — do **not** reduce, that needs a modulus and isn't needed.
- [ ] `seedBlockArgs` — felt-typed block arguments become signals
- [ ] `evalBody` — walk `blk.firstOp!` via `next!`; felt ops extend the env,
      `constrain.eq` contributes an equality pair
- [ ] `IRSat : IRContext → BlockPtr → Assignment p → Prop`
- [ ] `irsatb : ... → Bool` (executable twin) + a lemma connecting them
- [ ] `InFragment` predicate: every op in the body is in the modeled set.
      Take it as a hypothesis rather than returning `False` on unknown ops —
      it makes "what subset is verified" a checked property.

Everything is parameterized by `p`; theorems are `∀ p`. No field registry needed
(see Deferred).

Tests: `UnitTest/LLZK/Semantics.lean`, wired into `UnitTest.lean`.
Use the `/-- info: ... -/ #guard_msgs in #eval` style from
`UnitTest/ConstantValue.lean`.

Worked example to test against (parses in VeIR today, no new dialects needed):

```mlir
"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %0 = "felt.mul"(%a, %b)           : (!felt.type, !felt.type) -> !felt.type
  %1 = "felt.const"() <{value = 3}> : () -> !felt.type
  %2 = "felt.add"(%0, %1)           : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%2, %a)            : (!felt.type, !felt.type) -> ()
}) : () -> ()
```

means `a·b + 3 = a`. At `p = 7`: `(a,b) = (2,3)` satisfies, `(1,1)` does not.

---

## Phase 2 — Verified constraint deduplication

The first real verified LLZK pass. Chosen because every `eraseOp` precondition
discharges trivially: `constrain.eq` has **2 operands, 0 results, 0 regions**
(`Constrain.verifyLocalInvariants` → `verifyPlainOpCounts ctx opIn 2 0`), so
`!op.hasUses!` is free and no `replaceValue` is ever needed.

- [ ] `Veir/Passes/LLZK/DedupConstraints.lean`. Not a `LocalRewritePattern` —
      the match depends on *earlier* ops. Model it on `Veir/Passes/CSE.lean`,
      which is `Id.run do` + `let mut ctx` + `let mut seen`.
- [ ] Register in `VeirOpt.lean` `availablePasses`
- [ ] FileCheck test under `Test/LLZK/Constrain/passes/`
- [ ] **Theorem**: `IRSat ctx' blk σ ↔ IRSat ctx blk σ`

Proof shape: erasing a `constrain.eq` defines nothing, so `ValEnv` is unchanged
(via `OperationPtr.getOpType!_eraseOp`, `getOperands!_eraseOp`, `next!_eraseOp`,
`BlockPtr.firstOp!_eraseOp` — all proven, zero sorries in
`Veir/Rewriter/GetSet/DetachOp.lean`). The equality list loses one element,
which a surviving duplicate implies.

Note: CSE will **not** already do this — `constrain.eq` has
`getEffects := .write` (deliberately, so DCE doesn't delete the constraint
system), and CSE only handles memory-independent ops.

- [ ] Differential: compare against
      `~/veridise/llzk-lib/result/bin/llzk-opt --llzk-duplicate-op-elim`.
      Verified working this session. Use `scripts/llzk-diff.sh --lower-first`
      to bridge LLZK pretty syntax → generic MLIR (VeIR parses generic only).

---

## Phase 3 — Struct dialect

Needed to run on real circuits (`struct.readf %self[@f]`) and for degree
lowering (which *adds* members). **Struct has never existed in VeIR** — it was
not in the pre-merge monolithic file either, so there is nothing to recover.

- [ ] `Veir/Dialects/LLZK/Struct/Properties.lean`
      - `StructDefProperties { symName }`
      - `MemberDefProperties { symName, type, column, signal }`
      - `MemberReadProperties { memberName }` / `MemberWriteProperties`
- [ ] `Veir/Dialects/LLZK/Struct/OpInfo.lean` — opcodes `def`, `member`, `new`,
      `readm`, `writem`. `struct.def` needs `isIsolatedFromAbove := true`,
      `getRegionKind := .Graph`, `hasNoTerminator := true`.
      Template: `Veir/Dialects/LLZK/Felt/OpInfo.lean`.
- [ ] `!struct.type` in `Veir/IR/Attribute.lean` (~6 sites: inductive case,
      `DecidableEq`, `ToString`, `isType`, `isType` lemma, `IsTypeAttr`).
      Nominal type — carries only `nameRef` + optional params, **not** the field
      list, so no recursion and no cycles.
- [ ] Parser cases in `Veir/Parser/AttrParser.lean` (~3 sites)
- [ ] One `public import` line in `Veir/OpCode.lean` (that is the registration)
- [ ] Well-formedness predicate rejecting **open** struct types — require every
      template parameter to be a concrete `IntegerAttr`/`TypeAttr`, no
      `SymbolRefAttr`, no `AffineMapAttr`, no `!poly.tvar`. Keeps types closed
      terms; no substitution or unification machinery needed. The SP1 corpus is
      `struct.def @X<[]>` throughout, so it is 100% inside this fragment.
- [ ] Extend `IRSat` so `struct.readm %self[@f]` denotes a signal
- [ ] **Decide the mnemonic question** — see Open Questions.

Optional automation: `llvm-tblgen --dump-json` works today and emits the full
ODS record database. Verified this session:

```bash
/opt/homebrew/opt/llvm@20/bin/llvm-tblgen --dump-json \
  -I include -I /opt/homebrew/opt/llvm@20/include \
  include/llzk/Dialect/Struct/IR/Ops.td -o struct.json
```

Op mnemonics, arities, and traits are all recoverable; operands vs attributes
split on `!superclasses` containing `TypeConstraint` vs `AttrConstraint`.
Roughly 80% of an `OpInfo.lean`. Not derivable: `hasVerifier = 1` custom C++,
variadic operand segments, `extraClassDeclaration`. Write Struct by hand first,
then decide whether the generator is worth it.

---

## Phase 4 — Verified degree lowering

The flagship. `LLZKPolyLoweringPass.cpp` (1,095 LoC) is **not** pattern-based —
it is an imperative walk threading `DenseMap<Value,Value>& rewrites` and
`SmallVector<AuxAssignment>& auxAssignments` by reference. That is a state monad
written by hand; in Lean it becomes `Id.run do` + `let mut`, the same shape as
`CSE.lean`. The port is more mechanical than "not pattern-based" suggests.

Each extracted subexpression produces **three** IR edits:
1. a `struct.member` appended to the `struct.def` region
2. a `struct.writem` in `compute` (how the prover computes the aux value)
3. a `struct.readm` + `constrain.eq` in `constrain` (what pins it)

Edits (2) and (3) are the two directions of the existential.

- [ ] `⟦compute⟧ : Inputs → Option Witness`. Unlike `constrain`, `compute` is
      operational and fits VeIR's existing interpreter — needs `RuntimeValue.felt`
      and `Felt.interpretOp'` wired in (this is the `FOLLOWUP.md` F3 work).
      Template: `ModArith.interpretOp'` at `Veir/Interpreter/Basic.lean:737`,
      plus one arm in the dispatch at line 1649.
- [ ] `degreeOf : ValuePtr → Nat` — `signal ↦ 1`, `const ↦ 0`,
      `add/sub ↦ max`, `neg ↦ id`, `mul ↦ +`
- [ ] The pass itself, incl. `orderAuxAssignments` (topological sort of aux
      defs — required because `compute` writes must be dependency-ordered)
- [ ] **T2 (degree bound)**: `∀ eq ∈ constraints(C'), degree eq ≤ maxDegree`.
      Pure syntax, no semantics. **Prove this first** — it is a real theorem
      about the real pass and exercises the IR-walking machinery.
- [ ] **T1a**: `P σ → P' (σ ⊕ τ₀ σ)` — constructive, no solutions lost
- [ ] **T1b**: `P' (σ ⊕ τ) → P σ` — no solutions gained
- [ ] **T1c**: `P' (σ ⊕ τ) → τ = τ₀ σ` — no new witness freedom.
      This is the ZK-critical one: without it the pass could introduce
      under-constraining. Proof is induction on the topological order.
- [ ] **T3**: `(f' inp)|M = f inp ∧ (f' inp)|A = τ₀ (f inp)` — the new compute
      still produces the old witness, and produces exactly the forced aux values
- [ ] **T4**: aux members carry no `{llzk.pub}`. One-line side condition, but
      load-bearing — see Phase 5.

`_createOp` lemmas needed for this all exist, zero sorries in
`Veir/Rewriter/GetSet/CreateOp.lean` and `InsertOp.lean`.

---

## Phase 5 — Soundness preservation (corollary)

```lean
def Sound (C) : Prop :=
  (∀ inp, P (f inp) inp)                          -- completeness
∧ (∀ inp w, P w inp → w|pub = (f inp)|pub)        -- soundness
```

- [ ] `theorem polyLowering_preserves_sound : Sound C → Sound C'`

Derives from T1a + T1b + T3 + T4; no new proof burden. Completeness: T1a gives
a witness, T3 says `compute` produces exactly it. Soundness: T1b restricts a
solution, T4 says the public members did not change.

Composes across passes — verify dedup and degree lowering and the pipeline
preserves soundness by composing corollaries.

Scope note: this is soundness *relative to `compute`*. It does not say the
circuit computes the right thing — that is a per-circuit specification question
(ZKLean, Picus, hand proofs). The division of labour is: they establish a
circuit is correct, VeIR establishes the compiler does not destroy that.

---

## Deferred

- **`FieldEnv` / the felt registry.** Not needed. `typesUnify` has no `FeltType`
  case, so binary felt ops require *exactly equal* operand types — the field is
  uniform across any connected expression, guaranteed by the verifier. A
  multi-field module therefore decomposes into independent single-field
  circuits. `FieldEnv` would be consumed once at denotation time to partition
  and resolve primes; it never threads through `IRSat`. And the SP1 corpus is
  100% bare `!felt.type` (6,508,937 occurrences, zero named, zero
  `llzk.fields`), so there is no prime to resolve anyway.
- **Non-native ops.** `pow`, `uintdiv`, `sintdiv`, `umod`, `smod`, `inv`,
  `bit_*`, `shl`, `shr` all carry LLZK's `NotFieldNative` trait, gated by
  `function.allow_non_native_field_ops`, and are documented as "must be
  rewritten or folded into a constant after the flattening and unrolling pass."
  Zero uses in the SP1 corpus. Use their absence as the fragment boundary.
- **Range checks.** The one non-native idiom real circuits *do* use:
  `bool.cmp lt` + `cast.tofelt` + `constrain.eq _, 1`, 20,831 uses, all `lt`
  against a constant power of two. Model as a single `InRange : Expr → Nat → Prop`
  primitive over the canonical representative when needed.
- **Lookups.** `constrain.in` + `array.new` + `global.read`, 319 uses. VeIR's
  `Constrain` dialect has an in-source note that `in` is deferred until Array
  types land.
- **Arrays, POD, Polymorphic/templates, `function.call`, `{column}` +
  `tableOffset` affine maps** (VeIR has no `affineMapAttr` at all).
- **Literal reduction into `[0,p)`.** Purely representational — see Findings.

---

## Open questions

- **Mnemonics.** `result/bin/llzk-opt` (the only working binary) is the *old*
  dialect: `struct.field` / `struct.readf` / `veridise.lang = "llzk"`.
  The `include/` sources are the *new* one: `struct.member` / `struct.readm` /
  `llzk.lang`. `build/bin/llzk-opt` is broken (references a garbage-collected
  nix store path `llvm-debug-20.1.8-lib`). Doesn't matter for Phases 1–2 (felt
  and constrain mnemonics are stable), but Phase 3 has to pick. Probably worth
  fixing the build first so there is a current-syntax oracle.
- **Implicit signals.** `{signal}` now definitively marks witness variables, but
  the SP1 corpus predates it (23,409 members, 1,403 `{llzk.pub}`, zero
  `{signal}`), and `StructDefOp`'s docs say Main-component inputs are signals
  even when unmarked. Confirm the rule for absent annotations before building
  the denotation on it.
- **`felt.div` is field-native but `felt.inv` is not**, despite div being
  defined as multiply-by-inverse. Worth asking Veridise whether that is
  intentional.
- **`Field::addField` rejects re-declaration on *existence*, not on prime
  mismatch** (`lib/Util/Field.cpp:86`) — so parsing two modules that both
  declare `field<foo, 7>` with the *same* prime is a fatal error. Looks like a
  bug; the diagnostic prints `prior=`/`new=` as if it were checking for
  conflict.

---

## Findings worth not re-deriving

- **Constant folding is modulus-independent.** `const` denotes
  `Int.cast : ℤ → ZMod p`, a ring hom, so `const a ⊕ const b → const (a ⊕ b)`
  holds `∀p` with no field resolution. Only *reducing the literal into `[0,p)`*
  needs `p`, and that is representational (LLZK stores a fixed-width `APInt` at
  `field.bitWidth()`; VeIR stores unbounded `Int`).
- **LLZK's felt dialect has no canonicalization patterns at all** — `hasFolder = 1`
  and no `hasCanonicalizer`, zero `matchAndRewrite` in `lib/Dialect/Felt/IR/Ops.cpp`.
  So it does constant folding only, and only on *named registered* fields
  (`tryGetBinaryFoldData` bails on a null field name). On bare felt it is inert.
  Measured on the SP1 corpus: 48 foldable constant pairs out of 462,701 binops
  (negligible) but **29,151 algebraic-identity sites** LLZK cannot touch —
  16,425 `add x,0`, 9,654 `mul x,1`, 2,455 `mul x,0`, 617 `sub x,0`. That is
  ~6.3% of all felt binops, and VeIR's existing 15 sorry-free patterns cover them.
- **Therefore "C++-parity" is the wrong target** for `felt-combine` — matching
  parity means suppressing a verified optimizer to imitate a no-op. The existing
  `EXPECTED-DIVERGE` cases in the harness are VeIR doing work C++ does not do.
  Repoint the differential harness from "must match" to "must not disagree on
  anything C++ actually rewrites."
- **The `_eraseOp` lemmas needed for Phase 2 all exist**, zero sorries in
  `DetachOp.lean` (845 lines, 24 proven `_eraseOp` lemmas). The ones still marked
  "quite complex to state" are *all* use-def chain internals
  (`ValuePtr.getFirstUse!_eraseOp`, `OpOperandPtr.get!_eraseOp`,
  `BlockOperandPtr.get!_eraseOp`, `BlockArgumentPtr.get!_eraseOp`). `IRSat` walks
  *forward* and reads operands; it never traverses a use chain backward, so none
  of them block it. `FOLLOWUP.md`'s assessment here is stale.
- **VeIR parses generic MLIR form only.** No `assemblyFormat` equivalent. Every
  `.llzk` file needs `llzk-opt --mlir-print-op-generic` first.
- **The parser builds the IR directly** — no AST. `MlirParserState` carries
  `ctx : WfIRContext` and calls `WfRewriter.createOp` / `setBlockArguments` /
  `replaceValue` as it goes, using detached `unrealized_conversion_cast`
  placeholders for forward references, exactly like MLIR.
- **Unregistered ops and types round-trip.** Unknown ops become
  `builtin.unregistered` with the name in properties (behind
  `--allow-unregistered-dialect`); unknown types become `UnregisteredAttr` with
  `isType := true`. So you only pay registration cost for what you reason about.
- **Real circuits are tiny in op vocabulary.** SP1/plonky3 (47 files, 193MB)
  uses exactly: `felt.{add,mul,sub,const,neg}`, `constrain.{eq,in}`,
  `struct.{field,readf,new,def}`, `cast.tofelt` + `bool.cmp lt`, `array.new`,
  `global.{def,read}`, `function.{def,return}`. Zero `function.call`, zero
  `struct.writef`, zero `array.read/write`, zero `scf.*`, zero `poly.*`.
  `compute` is empty everywhere (1–8 ops, mostly just `struct.new`) — these are
  AIR-style circuits where members are trace columns.
- Circom-derived tests are a *different* sublanguage: `scf.for`, `function.call`,
  `poly.template`/`param`/`read_const`, `array.read/write`, `struct.writem`,
  `pod.*`, `llzk.nondet`. Which corpus you target decides how many layers you need.
