module

public import Veir.Dialects.LLZK.Analysis.Intervals
public import Veir.Dialects.LLZK.Semantics.Constraint

/-!
# LLZK range analysis

Port of the dataflow layer of `llzk-lib`'s interval analysis:
`include/llzk/Analysis/IntervalAnalysis.h` + `lib/Analysis/IntervalAnalysis.cpp`,
restricted to the block-level SP1 fragment from Phase 1 (`felt.const/add/sub/
mul/neg` + `constrain.eq`; block arguments are the signals).

**What drops out of the C++ and why:**

- The `SMTExprRef` half of `ExpressionValue` — its job is to let Z3 be the
  ground truth for facts intervals cannot express. Here `IRSat` is the ground
  truth, so the lattice value is just `Interval p` and the analysis state is
  `Std.HashMap ValuePtr (Interval p)`, the exact shape of `ValEnv`.
- `SourceRef` / `MemberMap` / `StructIntervals` — struct-layer, waits for M3.
- MLIR's `SparseForwardDataFlowAnalysis` fixpoint solver — the fragment is
  straight-line SSA, so one forward walk suffices. VeIR's own
  `DataFlowFramework.fixpointSolve` is not used either: its worklist `run` is
  `partial def`, kernel-opaque, so nothing routed through it is provable
  (the same trap as the `while`-loop `opsOf`, see the two-track rule).

**Driver discipline (same as Phase 1):** everything recurses structurally on a
`List OperationPtr` obtained from `opsOf`, so it is executable *and* provable,
and `opsOf_eq_operationList` bridges to the proof side when WF facts are
needed. `analyzeOps` mirrors `evalBody`'s recursion *branch for branch* —
that is load-bearing for Part H's lockstep induction; do not restructure one
without the other.

**This file is an exercise skeleton.** See `EXERCISES.md` Part G.
-/

namespace Veir.LLZK.Analysis

open Veir.LLZK.Semantics

public section

/-- The analysis state: what is known about each SSA value. Absence of a key
    means "no information", i.e. `Interval.entire` — look up with
    `M.getD v .entire` (the counterpart of the C++ `setToEntryState` /
    `createUnknownValue` defaults, IntervalAnalysis.h:347,373). -/
abbrev IntervalEnv (p : Nat) := Std.HashMap ValuePtr (Interval p)

/-- **Exercise G1.** Forward transfer for one op: the interval of its result,
    from the intervals of its operands. `none` for anything outside the
    fragment (and for `constrain.eq`, which has no result).

    Mirror `evalFeltOp` branch for branch — same `getOpType!`-first dispatch,
    same five cases:
    - `.felt .const` ↦ `.degenerate` of the literal (two property hops, as in
      `evalFeltOp`)
    - `.felt .add/.sub/.mul` ↦ the F7 op on `M.getD operand .entire`
    - `.felt .neg` ↦ `Interval.neg`

    C++ counterpart: `performBinaryArithmetic` / `performUnaryArithmetic`
    (IntervalAnalysis.cpp), minus the solver-expression plumbing. -/
def transferOp {p : Nat} (ctx : IRContext OpCode) (op : OperationPtr)
    (M : IntervalEnv p) : Option (Interval p) :=
  sorry

/-- **Exercise G2.** Seed the state for a block: every *felt* block argument
    starts at `.entire` (a signal can be anything until a constraint says
    otherwise). Mirror `seedBlockArgs`' loop shape, minus σ. -/
def seedArgIntervals (p : Nat) (ctx : IRContext OpCode) (blk : BlockPtr) :
    IntervalEnv p :=
  sorry

/-- **Exercise G3.** Backward refinement — the heart of the analysis.
    C++: `applyInterval` (IntervalAnalysis.cpp:1386).

    `applyInterval ctx fuel M v I` records that `v`'s value is *known* to lie
    in `I` (justified by a constraint), then pushes that knowledge backwards
    through `v.definingOp?`:

    1. Update `M[v] := (M.getD v .entire).intersect I`.
    2. If `fuel = 0` or `v.definingOp? = none` (block argument), stop.
    3. Otherwise match the defining op (C++ lines for each rule):
       - `.felt .add` — lhs gets `I.sub (M rhs)`, rhs gets `I.sub (M lhs)`;
         recurse into both (cpp:1588).
       - `.felt .sub` — lhs gets `I.add (M rhs)`, rhs gets `(M lhs).sub I`
         (cpp:1606).
       - `.felt .neg` — operand gets `I.neg`.
       - `.felt .mul` — if `¬ I.mem 0`, each operand gets
         `(M operand).difference (.degenerate 0)` (cpp:1540–1571: nonzero
         product means nonzero factors). The C++ also divides through by a
         degenerate factor there — that needs `feltDiv`; leave it for later.
       - `.felt .const`, anything else — stop (a constant's interval does not
         improve, cpp:1392).

    Fuel bounds the recursion instead of a dominance argument. That is
    principled here: every step *intersects with a justified interval*, so
    soundness (H2) is invariant under how many steps run and in what order —
    fuel only costs precision, which the theorem does not quantify. When VeIR
    grows an "operands dominate uses" WF fact, this can become structural
    recursion; do not block on it. -/
def applyInterval {p : Nat} (ctx : IRContext OpCode) (fuel : Nat)
    (M : IntervalEnv p) (v : ValuePtr) (I : Interval p) : IntervalEnv p :=
  sorry

/-- **Exercise G4.** Walk the body once, forward. Mirrors `evalBody` branch
    for branch (Part H does induction on the two in lockstep):

    - `.constrain .eq` — the constrained values must be equal, so both lie in
      the *intersection* of their intervals: `applyInterval` it to both
      operands (C++ `EmitEqualityOp` case, cpp:992). No entry is added — the
      op has no result.
    - otherwise — `transferOp`; on `some I` insert for `op.getResult 0`, on
      `none` recurse with `M` unchanged (unmodelled ops stay `entire`, which
      is sound; `evalBody` aborts there, so Part H never has to argue about
      that branch).

    The C++ also special-cases `(s−c₀)(s−c₁)⋯(s−cₙ) = 0` here
    (`getGeneralizedDecompInterval`, cpp:999,1716) — that rule is the one
    place needing `p` prime (no zero divisors). Leave it out of v1; it slots
    into this branch later. -/
def analyzeOps {p : Nat} (ctx : IRContext OpCode) (fuel : Nat)
    (ops : List OperationPtr) (M : IntervalEnv p) : IntervalEnv p :=
  sorry

/-- **Exercise G5.** Glue: seed, walk, done. Fuel: `(opsOf ctx blk).length`
    is a natural bound (a refinement chain cannot be longer than the block).

    Executable end-to-end: parse the Phase 1 worked example and `#eval` this
    with `p := 7` next to hand-computed intervals before touching Part H. -/
def rangeAnalysis (p : Nat) (ctx : WfIRContext OpCode) (blk : BlockPtr)
    (hblk : blk.InBounds ctx.raw := by grind) : IntervalEnv p :=
  sorry

end

end Veir.LLZK.Analysis
