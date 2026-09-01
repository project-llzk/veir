module

public import Veir.Dialects.LLZK.Analysis.RangeAnalysis

/-!
# Soundness of the LLZK range analysis

An analysis's correctness statement is different in kind from a pass's. Dedup
proves `IRSat` is *preserved*. An analysis proves its output *over-approximates
every solution*: for every σ with `IRSat ctx blk σ`, every value's concrete
value under σ lies in the interval the analysis computed for it. The C++ has no
counterpart to this file — this is the assurance the port adds.

Two corollaries fall out and are the point of running the analysis at all:
- an `empty` interval on a signal proves the circuit **unsatisfiable** — the
  C++ over-constrained warning becomes a theorem (H5);
- a `degenerate` interval proves the signal is **fixed** in every solution (H6).

The invariants `Consistent` and `EnvClosed` below are given — they are the
sketch's load-bearing design. Read them before proving anything. Everything
else is yours. Expect the *hypotheses* of H2/H3 to need iteration once you are
inside the induction — that is normal; the conclusions should survive.

Note what is *not* assumed: `p` prime. No v1 rule needs it — the backward
multiplication rule is "product avoids 0 ⇒ factors avoid 0", whose contrapositive
is `zero_mul`. Primality enters only with the generalized decomposition rule
`(s−c₀)⋯(s−cₙ) = 0 ⇒ s ∈ {c₀…cₙ}` (no zero divisors) and `feltDiv` — when
those land, `[Fact p.Prime]` appears on exactly the theorems that use them.

**This file is an exercise skeleton.** See `EXERCISES.md` Part H.
-/

namespace Veir.LLZK.Analysis

open Veir.LLZK.Semantics

public section

/-- The analysis state is consistent with a value environment: whenever both
    have an entry for `v`, the concrete value lies in the interval. This is
    the invariant threaded through every step of Part H. -/
def Consistent {p : Nat} (Γ : ValEnv p) (M : IntervalEnv p) : Prop :=
  ∀ (v : ValuePtr) (I : Interval p) (x : ZMod p),
    M[v]? = some I → Γ[v]? = some x → I.mem x

/-- The value environment is closed under defining ops: an entry for an op
    result is what `evalFeltOp` computes from the (final) environment. This is
    what lets `applyInterval` walk backwards — `Consistent` alone says nothing
    about how `Γ[v]` relates to `Γ` at `v`'s operands.

    `evalBody` produces a closed environment: each insert is exactly
    `evalFeltOp` of the prefix env, later inserts only *add* keys (SSA — no
    result is defined twice), and lookups are stable under key-adding inserts.
    Expect the "no result is defined twice" step to need a WF fact; go mining
    in `Veir/IR/WellFormed.lean` before proving it from scratch. -/
def EnvClosed {p : Nat} (ctx : IRContext OpCode) (Γ : ValEnv p) : Prop :=
  ∀ (v : ValuePtr) (op : OperationPtr) (x : ZMod p),
    v.definingOp? = some op → Γ[v]? = some x →
    evalFeltOp ctx op Γ = some x

/-- **Exercise H1.** Forward transfer is sound. Case analysis mirroring the
    shared branch structure of `transferOp`/`evalFeltOp`, one F8 lemma per
    branch (`const` ↦ `mem` of `degenerate` directly). -/
theorem transferOp_sound {p : Nat} (ctx : IRContext OpCode) (op : OperationPtr)
    (Γ : ValEnv p) (M : IntervalEnv p) (hc : Consistent Γ M)
    (x : ZMod p) (hx : evalFeltOp ctx op Γ = some x)
    (I : Interval p) (hI : transferOp ctx op M = some I) :
    I.mem x := by
  sorry

/-- **Exercise H2a.** The backward multiplication rule's arithmetic content:
    a factor of a product known to avoid `0` itself avoids `0`. No primality —
    the contrapositive is `zero_mul`. Composes `Interval.mem_difference` with
    that observation. The other backward rules (add/sub/neg) need no new
    lemmas at all: solving `x + y ∈ I` for `x` *is* `Interval.mem_sub`
    applied to `(x + y) - y`, plus `ring_nf`. -/
theorem Interval.mem_exclude_zero {p : Nat} (ix res : Interval p) (x y : ZMod p)
    (hx : ix.mem x) (hres : res.mem (x * y)) (h0 : ¬ res.mem 0) :
    (ix.difference (.degenerate 0)).mem x := by
  sorry

/-- **Exercise H2.** Backward refinement is sound: if the applied interval is
    *justified* (every value `v` can take under Γ lies in it), consistency
    survives — for any fuel. Induction on `fuel`; each rule's step is
    "intersect with a justified interval", where the justification for the
    operand-level recursive calls comes from `EnvClosed` + the F8/H2a lemmas.

    This is why fuel is principled: the statement quantifies over all fuel,
    so termination of the C++ recursion never has to be argued. -/
theorem applyInterval_sound {p : Nat} (ctx : IRContext OpCode) (fuel : Nat)
    (Γ : ValEnv p) (M : IntervalEnv p)
    (hc : Consistent Γ M) (hcl : EnvClosed ctx Γ)
    (v : ValuePtr) (I : Interval p)
    (hjust : ∀ x : ZMod p, Γ[v]? = some x → I.mem x) :
    Consistent Γ (applyInterval ctx fuel M v I) := by
  sorry

/-- **Exercise H3.** The walk is sound — the lockstep induction. `analyzeOps`
    and `evalBody` recurse on the same list with the same branch structure
    (by construction, G4), so a single induction on `ops` steps both:

    - felt-op step: `Γ` gains a binding justified by `evalFeltOp`, `M` gains
      one justified by H1; `Consistent`/`EnvClosed` survive via the HashMap
      insert lemmas.
    - `constrain.eq` step: `hcs` (head) gives `lhs = rhs`; both values
      therefore lie in both intervals, hence in the intersection —
      `Interval.mem_intersect` justifies the two `applyInterval` calls, H2
      closes them.

    Subtlety to expect: the `Consistent`/`EnvClosed` hypotheses talk about the
    env *at this step*, but H2's justification needs values under the *final*
    Γ. Strengthen the induction hypothesis (state it for every suffix, as
    `op_chain_eq_drop` quantified `i` inside) rather than fighting it. -/
theorem analyzeOps_sound {p : Nat} (ctx : IRContext OpCode) (fuel : Nat)
    (ops : List OperationPtr)
    (Γ₀ Γ : ValEnv p) (cs : List (ZMod p × ZMod p)) (M₀ : IntervalEnv p)
    (heval : evalBody ctx ops Γ₀ = some (Γ, cs))
    (hcs : ∀ lhs rhs : ZMod p, (lhs, rhs) ∈ cs → lhs = rhs)
    (hc : Consistent Γ₀ M₀) (hcl : EnvClosed ctx Γ₀) :
    Consistent Γ (analyzeOps ctx fuel ops M₀) := by
  sorry

/-- **Exercise H4.** The headline theorem: the analysis over-approximates
    every satisfying assignment. Unfold `IRSat` to expose `evalBody` and the
    all-pairs-equal fact, seed `Consistent`/`EnvClosed` for
    `seedBlockArgs` (block args have no defining op, so `EnvClosed` is
    near-vacuous there), bridge `opsOf` ↔ `operationList` with
    `opsOf_eq_operationList`, and hand everything to H3. -/
theorem rangeAnalysis_sound {p : Nat} (ctx : WfIRContext OpCode)
    (blk : BlockPtr) (hBlock : blk.InBounds ctx.raw)
    (σ : Assignment p) (hsat : IRSat ctx blk hBlock σ)
    (Γ : ValEnv p) (cs : List (ZMod p × ZMod p))
    (heval : evalBody ctx.raw (blk.operationList ctx.raw).toList
        (seedBlockArgs ctx.raw blk σ) = some (Γ, cs)) :
    Consistent Γ (rangeAnalysis p ctx blk hBlock) := by
  sorry

/-- **Exercise H5.** The over-constrained corollary: an `empty` interval on a
    felt block argument (a signal) refutes satisfiability outright.

    From H4: any satisfying σ yields a Γ that binds every felt block argument
    (that is `seedBlockArgs`' loop, and `evalBody` only adds keys), and
    `Consistent` then demands `Interval.empty.mem x` — false by F5. -/
theorem unsat_of_empty_arg (p : Nat) (ctx : WfIRContext OpCode)
    (blk : BlockPtr) (hBlock : blk.InBounds ctx.raw)
    (v : ValuePtr)
    (hargmem : v ∈ blk.getArguments! ctx.raw)
    (hty : ∃ ft, (v.getType! ctx.raw).val = .feltType ft)
    (hempty : (rangeAnalysis p ctx blk hBlock)[v]? = some .empty) :
    ¬ ∃ σ : Assignment p, IRSat ctx blk hBlock σ := by
  sorry

/-- **Exercise H6.** The fixed-signal corollary: a `degenerate` interval pins
    a value in every solution. Immediate from H4 plus F5's `degenerate`
    clause. -/
theorem value_fixed_of_degenerate {p : Nat} (ctx : WfIRContext OpCode)
    (blk : BlockPtr) (hBlock : blk.InBounds ctx.raw)
    (σ : Assignment p) (hsat : IRSat ctx blk hBlock σ)
    (Γ : ValEnv p) (cs : List (ZMod p × ZMod p))
    (heval : evalBody ctx.raw (blk.operationList ctx.raw).toList
        (seedBlockArgs ctx.raw blk σ) = some (Γ, cs))
    (v : ValuePtr) (c : Int)
    (hdeg : (rangeAnalysis p ctx blk hBlock)[v]? = some (.degenerate c))
    (x : ZMod p) (hx : Γ[v]? = some x) :
    x = (c : ZMod p) := by
  sorry

end

end Veir.LLZK.Analysis
