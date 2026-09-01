module

public import Mathlib.Data.ZMod.Basic
public import Veir.Analysis.DataFlow.Domains.AbstractDomain

/-!
# LLZK interval domain

Port of the interval lattice behind `llzk-lib`'s interval analysis:
`include/llzk/Analysis/Intervals.h` + `lib/Analysis/Intervals.cpp`.

Two layers, mirroring the C++:

- `UnreducedInterval` — a plain integer interval `[lo, hi]`, not bound to any
  field. All arithmetic happens here, over ℤ, where it is exact.
- `Interval p` — an interval *reduced* into the field `ZMod p`. Ops convert to
  the unreduced layer, operate, and `reduce` back.

**Deltas from the C++, both deliberate:**

- The C++ `UnreducedInterval` encodes "empty" as `a > b`. Here the struct
  carries `lo_le_hi`, and operations that can produce an empty result return
  `Option UnreducedInterval` with `none` for empty (the `IntegerRange` /
  `IntegerRangeLattice.bottom` idiom from
  `Veir/Dialects/ModArith/Analysis/RangeAnalysis.lean`).
- The C++ `Interval` has seven type tags (`Empty/Degenerate/TypeA/TypeB/TypeC/
  TypeF/Entire`). v1 collapses these to four: `internal` covers TypeA∪B∪C (a
  reduced, non-wrapping range) and TypeF (wrapping) widens to `entire`. That is
  *sound* — just imprecise — because concretization is uniform (see
  `Interval.mem`). The A/B/C/F distinction is purely a precision device and can
  be reintroduced later without touching the soundness statements. On the SP1
  corpus every range check is `[0, 2^k − 1]`, i.e. `internal`, so v1 loses
  nothing on the target circuits.

Oracle: `~/veridise/llzk-lib/unittests/Analysis/IntervalTests.cpp` — every
expectation there is a `#eval`/`decide` candidate against a concrete `p`.

**This file is an exercise skeleton.** See `EXERCISES.md` Part F. Signatures
and theorem statements are given; bodies are yours.
-/

namespace Veir.LLZK.Analysis

public section

/-! ## The unreduced layer — integer intervals, no field involved -/

/-- A nonempty closed integer interval `[lo, hi]`.

    C++ counterpart: `UnreducedInterval` (Intervals.h:26). Empty intervals are
    represented as `none : Option UnreducedInterval` at use sites, never as
    `lo > hi`. -/
structure UnreducedInterval where
  lo : Int
  hi : Int
  lo_le_hi : lo ≤ hi
deriving BEq, DecidableEq, Repr

namespace UnreducedInterval

/-- **Exercise F1.** Concretization: which integers does the interval denote? -/
def mem (u : UnreducedInterval) (k : Int) : Prop := u.lo ≤ k ∧ k ≤ u.hi

/-- Number of integers in the interval. C++: `width()` (Intervals.cpp). -/
def width (u : UnreducedInterval) : Int := u.hi - u.lo + 1

/-- **Exercise F2a.** Pointwise negation: `-[lo, hi] = [-hi, -lo]`.
    C++: `operator-()` (unary). -/
def neg (u : UnreducedInterval) : UnreducedInterval :=
  {-u.hi, -u.low, lower_le_upper := by grind}

/-- **Exercise F2b.** `[a,b] + [c,d] = [a+c, b+d]`. The `lo_le_hi` obligation
    is `omega` from the two component proofs — see
    `IntegerRangeLattice.addRange` in the ModArith file for the shape. -/
def add (u v : UnreducedInterval) : UnreducedInterval :=
  sorry

/-- **Exercise F2c.** Subtraction. Definable as `u.add v.neg`; if you do that,
    F3's `mem_sub` should fall out of `mem_add` + `mem_neg`. -/
def sub (u v : UnreducedInterval) : UnreducedInterval :=
  sorry

/-- **Exercise F2d.** Multiplication: min/max over the four corner products.

    Hint: do NOT copy `IntegerRangeLattice.mulRange`'s `Array.foldl` over a
    literal — `candidates[0]!` and `foldl` are proof-hostile (no useful
    equation lemmas at each corner). Write nested `min`/`max` of the four
    products directly; then F3's `mem_mul` is a finite case analysis that
    `rcases`/`nlinarith` (or a long `omega`-adjacent grind) can see through. -/
def mul (u v : UnreducedInterval) : UnreducedInterval :=
  sorry

/-! **Exercise F3.** Soundness of the unreduced ops. These four are pure
    integer inequalities — Mathlib's `mul_le_mul` family and `nlinarith` are
    your friends for `mem_mul`, `omega` handles the rest. -/

theorem mem_neg (u : UnreducedInterval) (k : Int) (h : u.mem k) :
    u.neg.mem (-k) := by
  sorry

theorem mem_add (u v : UnreducedInterval) (k l : Int)
    (hk : u.mem k) (hl : v.mem l) : (u.add v).mem (k + l) := by
  sorry

theorem mem_sub (u v : UnreducedInterval) (k l : Int)
    (hk : u.mem k) (hl : v.mem l) : (u.sub v).mem (k - l) := by
  sorry

theorem mem_mul (u v : UnreducedInterval) (k l : Int)
    (hk : u.mem k) (hl : v.mem l) : (u.mul v).mem (k * l) := by
  sorry

/-- **Exercise F4a.** Intersection; `none` when disjoint.
    C++: `intersect` (Intervals.cpp). Shape: `IntegerRangeLattice.meet`. -/
def intersect (u v : UnreducedInterval) : Option UnreducedInterval :=
  sorry

/-- **Exercise F4b.** Convex hull of the union. C++: `doUnion`. Always
    nonempty. Note it over-approximates: `[0,1] ∪ [5,6] ⊆ [0,6]`. -/
def union (u v : UnreducedInterval) : UnreducedInterval :=
  sorry

theorem mem_intersect (u v w : UnreducedInterval) (k : Int)
    (hw : u.intersect v = some w) : w.mem k ↔ u.mem k ∧ v.mem k := by
  sorry

theorem intersect_none (u v : UnreducedInterval) (k : Int)
    (hnone : u.intersect v = none) : ¬(u.mem k ∧ v.mem k) := by
  sorry

theorem mem_union_left (u v : UnreducedInterval) (k : Int) (h : u.mem k) :
    (u.union v).mem k := by
  sorry

theorem mem_union_right (u v : UnreducedInterval) (k : Int) (h : v.mem k) :
    (u.union v).mem k := by
  sorry

end UnreducedInterval

/-! ## The reduced layer — intervals over `ZMod p` -/

/-- An interval over the field `ZMod p`.

    C++ counterpart: `Interval` (Intervals.h:206), with the seven-way type tag
    collapsed to four (see the file docstring):

    - `empty`        ↔ C++ `Empty`
    - `degenerate v` ↔ C++ `Degenerate` — exactly the value `↑v`
    - `internal lo hi` ↔ C++ `TypeA`/`TypeB`/`TypeC` — a reduced range with
      `0 ≤ lo ≤ hi < p` (invariant maintained by `reduce`, not carried in the
      constructor; nothing below depends on it for *soundness*)
    - `entire`       ↔ C++ `Entire`, and the v1 widening of C++ `TypeF` -/
inductive Interval (p : Nat) where
  | empty
  | degenerate (v : Int)
  | internal (lo hi : Int)
  | entire
deriving BEq, DecidableEq, Repr

namespace Interval

/-- **Exercise F5.** Concretization into the field.

    The load-bearing design choice of the whole file: an interval denotes the
    *image of its integer range under the cast* `Int → ZMod p`:

    - `empty`          — nothing
    - `degenerate v`   — `x = ↑v`
    - `internal lo hi` — `∃ k : Int, lo ≤ k ∧ k ≤ hi ∧ ↑k = x`
    - `entire`         — everything

    This makes every `mem_*` lemma a statement about `Int.cast` (a ring hom —
    `push_cast` moves goals back to ℤ where F3 applies), works for every `p`
    including `0`, and is exactly the γ that would make the C++ wraparound
    types (`TypeB ≈ [-4,-2]`, etc.) meaningful if/when you add them back. -/
def mem {p : Nat} (i : Interval p) (x : ZMod p) : Prop :=
  sorry

/-- **Exercise F6.** Reduce an integer interval into the field.
    C++: `UnreducedInterval::reduce` (Intervals.cpp).

    The intended cases, in order:
    1. `u.width ≥ p` (and `p > 0`) — the range covers every residue: `entire`.
    2. `u.lo = u.hi` — `degenerate u.lo`.
    3. Otherwise reduce both endpoints with `Int.emod · p` into `[0, p)`:
       if `lo' ≤ hi'` the range does not wrap — `internal lo' hi'`;
       if it wraps (C++ TypeF/D/E territory) — v1 gives up: `entire`.

    Sanity: for `p = 0` case 1 never fires and `emod 0` is the identity, so
    check your branches still return something sound there (`mem_reduce` below
    is stated for all `p` on purpose). -/
def _root_.Veir.LLZK.Analysis.UnreducedInterval.reduce
    (p : Nat) (u : UnreducedInterval) : Interval p :=
  sorry

/-- **Exercise F6, the theorem.** Reduction is sound: every integer the
    unreduced interval contains lands, after casting, in the reduced interval.
    This is the single bridge between the two layers — every `mem_*` lemma
    below composes an F3 lemma with this one. -/
theorem _root_.Veir.LLZK.Analysis.UnreducedInterval.mem_reduce
    (p : Nat) (u : UnreducedInterval) (k : Int) (h : u.mem k) :
    (u.reduce p).mem ((k : ZMod p)) := by
  sorry

/-! **Exercise F7.** Field-interval arithmetic, via the unreduced layer.

    Shape for each binary op: dispatch `empty` (absorbing) and `entire`
    (dominating) first, then convert `degenerate v ↦ [v,v]` /
    `internal lo hi ↦ [lo,hi]` to `UnreducedInterval`, apply the F2 op, and
    `reduce`. C++: the `operator+`/`-`/`*` friends in Intervals.cpp — note the
    C++ also special-cases degenerates for precision; you can too, later. -/

def neg {p : Nat} (i : Interval p) : Interval p :=
  sorry

def add {p : Nat} (i j : Interval p) : Interval p :=
  sorry

def sub {p : Nat} (i j : Interval p) : Interval p :=
  sorry

def mul {p : Nat} (i j : Interval p) : Interval p :=
  sorry

/-- Intersection. C++: `Interval::intersect`. With only non-wrapping
    constructors this is the unreduced intersection, `none ↦ empty`. -/
def intersect {p : Nat} (i j : Interval p) : Interval p :=
  sorry

/-- Union/join. C++: `Interval::join`. Unreduced hull, plus tag dispatch. -/
def join {p : Nat} (i j : Interval p) : Interval p :=
  sorry

/-- Interval difference, `i` minus (`i` ∩ `j`). C++: `Interval::difference`
    (Intervals.h:286) — and read the comment there: when the true difference
    is two disjoint pieces the C++ returns `i` unchanged. That is sound only
    because `difference` promises an *over*-approximation; `mem_difference`
    below is exactly that contract, and your implementation must satisfy it
    (returning `i` always is a legal, zero-precision start). Used by the
    backward multiplication rule to knock `0` out of an operand's interval. -/
def difference {p : Nat} (i j : Interval p) : Interval p :=
  sorry

/-! **Exercise F8.** Soundness of the field-interval ops. Each is: unfold
    `mem`, pull the witness integer(s), apply the F3 lemma, finish with
    `mem_reduce` and `push_cast`. -/

theorem mem_neg {p : Nat} (i : Interval p) (x : ZMod p)
    (hx : i.mem x) : i.neg.mem (-x) := by
  sorry

theorem mem_add {p : Nat} (i j : Interval p) (x y : ZMod p)
    (hx : i.mem x) (hy : j.mem y) : (i.add j).mem (x + y) := by
  sorry

theorem mem_sub {p : Nat} (i j : Interval p) (x y : ZMod p)
    (hx : i.mem x) (hy : j.mem y) : (i.sub j).mem (x - y) := by
  sorry

theorem mem_mul {p : Nat} (i j : Interval p) (x y : ZMod p)
    (hx : i.mem x) (hy : j.mem y) : (i.mul j).mem (x * y) := by
  sorry

theorem mem_intersect {p : Nat} (i j : Interval p) (x : ZMod p)
    (hi : i.mem x) (hj : j.mem x) : (i.intersect j).mem x := by
  sorry

theorem mem_join_left {p : Nat} (i j : Interval p) (x : ZMod p)
    (hx : i.mem x) : (i.join j).mem x := by
  sorry

theorem mem_join_right {p : Nat} (i j : Interval p) (x : ZMod p)
    (hx : j.mem x) : (i.join j).mem x := by
  sorry

theorem mem_difference {p : Nat} (i j : Interval p) (x : ZMod p)
    (hx : i.mem x) (hj : ¬ j.mem x) : (i.difference j).mem x := by
  sorry

/-! ## Exercise F9 (optional, do last) — the house `AbstractDomain` instance

    Plugs `Interval p` into `Veir/Analysis/DataFlow/Domains/AbstractDomain.lean`
    so it is a first-class citizen of the upstream dataflow framework. Not
    needed by Parts G/H — the soundness theorem only uses `mem` — but it is
    what upstreaming will want. Model: `ConstantDomain.lean`, copied almost
    field-for-field.

    Gotcha: this file imports both Mathlib (via ZMod) and Veir's order
    typeclasses, which *both* define `⊤`/`⊥`/`⊔` notation and `Top`/`Bot`/
    `Join`/`Set`. Inside `namespace Veir.…` the Veir ones win, but if an
    ambiguous-notation error appears, write `Veir.Top.top` etc. explicitly. -/

/-- The abstraction order: `i ≤ j` iff `j` denotes at least what `i` does,
    decided syntactically (empty below everything, everything below entire,
    ranges by inclusion, degenerate as a one-point range). -/
def le {p : Nat} (i j : Interval p) : Prop :=
  sorry

instance {p : Nat} : LE (Interval p) := ⟨le⟩

instance {p : Nat} : BoundedOrder (Interval p) where
  top := .entire
  bot := .empty
  le_top := sorry
  bot_le := sorry

instance {p : Nat} : JoinSemilattice (Interval p) where
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry
  join := join
  le_join_left := sorry
  le_join_right := sorry
  join_le := sorry

instance {p : Nat} : AbstractDomain (Interval p) (ZMod p) where
  toJoinSemilattice := inferInstance
  toBoundedOrder := inferInstance
  γ := fun i x => i.mem x
  γ_top := sorry
  γ_bot := sorry
  γ_monotone := sorry

end Interval

end

end Veir.LLZK.Analysis
