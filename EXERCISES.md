# Learning track: LLZK constraint semantics in VeIR

Work through these yourself. The skeleton is
`Veir/Dialects/LLZK/Semantics/Constraint.lean` — signatures are given, bodies
are `sorry`. When you finish, you have the Phase 1 deliverable from
[`TODO.md`](TODO.md), not a throwaway tutorial.

## How to work

1. Open the skeleton in your IDE. The Lean LSP typechecks as you type — that is
   your fastest feedback loop, much faster than `lake build`.
2. Replace one `sorry` at a time. A `sorry` compiles, so the rest of the file
   keeps checking while you work.
3. `#eval` liberally. `#print` and `#check` too. Hover over anything to see its
   type.
4. When stuck, ask me — but say which level you want:
   - **"nudge"** — one sentence pointing at the idea
   - **"hint"** — the shape of the answer, not the answer
   - **"show me"** — the code, with an explanation
   I will default to *nudge* unless you say otherwise.
5. Paste errors verbatim. Lean's messages are precise and I would rather read
   the real one than guess.

## Before you start

You need a working build. `lake exe cache get` (Mathlib, the big download) then
`lake build`. The tree does build — a full build ran at 10:06–10:24 on
2026-08-26, all four binaries produced, and the Felt proof files compiled. So
this should be quick. See Phase 0 in `TODO.md` for the checks that *are* still
worth running (lit, and `#print axioms`), since compiling is not the same as
proved.

---

## Part A — Lean warm-up (no IR)

Three exercises on a toy expression tree. The point is to get the two core
skills — structural recursion and `simp`-style proof — without also fighting
IR accessors.

### A1 — `FeltExpr.eval`

Structural recursion with pattern matching.

- Match on the constructor, recurse on subterms.
- For `const n`, you want the ring hom `ℤ → ZMod p`. In Lean that coercion is
  written `(n : ZMod p)`.
- Lean will accept `| .sig s => σ s` style pattern arms directly after the `:=`.

Check yourself:

```lean
#eval (FeltExpr.add (.sig 0) (.const 3)).eval (p := 7) (fun _ => 2)
-- expect 5
#eval (FeltExpr.mul (.sig 0) (.sig 0)).eval (p := 7) (fun _ => 3)
-- expect 2   (9 mod 7)
```

### A2 — `eval_add_const_zero`

Your first proof. `x + 0 = x`, lifted through `eval`.

- `simp [FeltExpr.eval]` unfolds the definition. See how far that gets you.
- If it leaves a goal about `ZMod p` arithmetic, `ring` closes it.
- Note what is *not* needed: no primality, no field name, no modulus. This holds
  in every `ZMod p`, which is exactly why `felt-combine` can fire on bare
  `!felt.type`.

### A3 — `eval_const_add`

Constant folding, modulus-independent.

- The content is `Int.cast_add : ((a + b : ℤ) : R) = a + b`. `push_cast` is the
  tactic that applies cast lemmas like this; `simp` may find it too.
- This is the theorem behind the `TODO.md` finding that VeIR can fold constants
  on bare felt where LLZK's C++ folder declines to — LLZK reduces at the same
  time it folds, and reduction needs a prime.

**Stop here and tell me when A is done.** Part B is a step up and I would rather
calibrate on what A felt like.

---

## Part B — walking the IR

Now the real thing. These need VeIR's accessors, which take the context
explicitly: `op.getOpType! ctx`, `op.getOperands! ctx`, `op.next! ctx`.

### B1 — `opsOf`

A block's operations are an intrusive **linked list**, not an array.

- Start at `blk.firstOp! ctx`, follow `op.next! ctx` until `none`.
- Write it in VeIR's house style: `Id.run do` with `let mut`. Read
  `Veir/Passes/CSE.lean` around line 148 first — it is exactly this shape and
  it is the file you are about to imitate again in Part D.
- Lean must see termination. If the structure fights you, `partial def` is a
  legitimate escape for now; you can tighten it later.

Check: parse the worked example from `TODO.md` Phase 1 and confirm you get four
operations.

### B2 — `evalFeltOp`

The heart of it. One case per field-native felt op.

- `op.getOpType! ctx` returns an `OpCode`; you match on `.felt .add` etc.
- Everything outside `{const, add, sub, mul, neg}` returns `none`. That set is
  not arbitrary: it is exactly LLZK's field-native fragment, the ops *without*
  the `NotFieldNative` trait.
- For `.felt .const`, the value lives in the properties. Look at
  `Veir/Dialects/LLZK/Felt/OpInfo.lean` to see how `propertiesOf` maps `.const`
  to `FeltConstProperties`, and `Veir/IR/Attribute.lean` for its `value : Int`.
- `do` notation over `Option` makes the operand lookups readable:
  `do return (← env[a]?) + (← env[b]?)`.

### B3 — `seedBlockArgs`

Signals are the felt-typed block arguments. Argument `i` gets `σ i`.

- `blk.getNumArguments! ctx` gives the count.
- The `ValuePtr` for argument `i` is a `.blockArgument ⟨blk, i⟩`.
- You may want to filter on the argument type being `!felt.type` — an `i32`
  argument is not a signal. Decide what to do with non-felt arguments and write
  a comment saying which you chose.

### B4 — `evalBody`

Put B1–B3 together: fold over the op list, extending `env` for felt ops and
accumulating a pair for each `constrain.eq`.

- `constrain.eq` has **two operands and zero results**
  (`Constrain.verifyLocalInvariants` → `verifyPlainOpCounts ctx opIn 2 0`), so
  it contributes to the equality list and never to `env`.
- Return `none` on any unmodelled op, for now. Part E replaces that with a
  proper well-formedness hypothesis.

---

## Part C — satisfaction

### C1 / C2 — `IRSat` and `irsatb`

`IRSat` is a `Prop`: the mathematical statement theorems are about. `irsatb` is
a `Bool`: what `#eval` can run.

Write them **structurally parallel** — same shape, one returning
`∀ pr ∈ eqs, pr.1 = pr.2` and one returning `eqs.all (fun pr => pr.1 == pr.2)`.
If they diverge in structure, C3 becomes painful for no reason.

### C3 — they agree

If C1 and C2 are parallel, this should be close to
`simp [IRSat, irsatb, List.all_eq_true]`. If it is a fight, that is a signal to
go back and align the definitions rather than to push harder on the proof.

Then write real tests in `UnitTest/LLZK/Semantics.lean`, wired into
`UnitTest.lean`. Copy the `/-- info: ... -/ #guard_msgs in #eval` pattern from
`UnitTest/ConstantValue.lean`.

Target: the worked example from `TODO.md`, which means `a·b + 3 = a`. At
`p = 7`, `(a,b) = (2,3)` satisfies it and `(1,1)` does not.

---

## Part D — the dedup pass (Phase 2)

New file, `Veir/Passes/LLZK/DedupConstraints.lean`. No skeleton — by here you
should be writing from scratch, with `Veir/Passes/CSE.lean` as the model.

1. Walk the block keeping a `Std.HashSet (ValuePtr × ValuePtr)` of seen operand
   pairs.
2. On a repeat, `WfRewriter.eraseOp`.
3. Register it in `VeirOpt.lean`'s `availablePasses`.
4. FileCheck test under `Test/LLZK/Constrain/passes/`.
5. Differential against
   `~/veridise/llzk-lib/result/bin/llzk-opt --llzk-duplicate-op-elim`
   (that binary works; `build/bin/llzk-opt` is broken).

Two things you will hit, so know them now:

- `eraseOp` demands `getNumRegions! = 0` and `!op.hasUses!`. For `constrain.eq`
  both are *trivially* true — zero regions, zero results. This is precisely why
  it is the right first pass.
- CSE will not already have done this: `constrain.eq` carries
  `getEffects := .write` (deliberately, so DCE cannot delete the constraint
  system), and CSE only considers memory-independent ops.

---

## Part E — the theorem (Phase 2, continued)

```lean
theorem dedup_preserves_IRSat {p : Nat} (σ : Assignment p) … :
    IRSat ctx' blk σ ↔ IRSat ctx blk σ
```

The argument in words, which you then turn into Lean:

1. The erased op defines nothing, so `env` is **bit-for-bit identical**. This is
   where the `_eraseOp` lemmas earn their keep — `getOpType!_eraseOp`,
   `getOperands!_eraseOp`, `next!_eraseOp`, `firstOp!_eraseOp`. All proven, zero
   sorries in `Veir/Rewriter/GetSet/DetachOp.lean`.
2. The equality list loses exactly one element.
3. That element duplicates one still present, so the conjunction is unchanged.

Expect step 1 to be most of the work, and expect to need an `InFragment`
hypothesis before it goes through cleanly. That is the point at which the
`| none => False` shortcut from B4 stops paying and you replace it.

---

## What to ask me for

- **Running things.** Builds, tests, `llzk-opt` comparisons, git archaeology —
  hand those to me, they are not what you are trying to learn.
- **Errors.** Paste them. Lean's are specific.
- **"Is this idiomatic?"** — worth asking. There is usually a shorter way, and
  matching VeIR's house style matters for upstreaming.
- **Design questions.** "Should `seedBlockArgs` skip non-felt arguments?" is a
  real question with consequences, not a Lean question.

What I will not do unless you ask: fill in the `sorry`s.
