module

public import Veir.Passes.LLZK.DedupConstraints

/-!
# Correctness of constraint deduplication

The goal:

    IRSat (dedupBlock ctx blk hblk) blk hblk' σ ↔ IRSat ctx blk hblk σ

Erasing a repeated `constrain.eq` defines no value, so the `ValEnv` is untouched;
the constraint list loses one pair, and a surviving earlier copy of that pair
carries the same obligation. Hence satisfaction is unchanged.

The proof decomposes into three independent pieces. The third is the semantic
core and is proved here; the first two are IR-level and are the remaining work.
-/

namespace Veir
namespace LLZK
namespace DedupConstraints

open Veir.LLZK.Semantics

public section

/-! ## Piece 3 — the semantic core (proved)

Dropping one element from the constraint list changes nothing, provided an
equal element survives. This is where "duplicates are redundant" actually
lives, and it needs no IR at all. -/

/-- If every pair in `l` agrees then so does every pair in any sublist. -/
theorem all_eq_of_sublist {p : Nat} {l l' : List (ZMod p × ZMod p)}
    (hsub : l'.Sublist l) (h : ∀ q ∈ l, q.1 = q.2) : ∀ q ∈ l', q.1 = q.2 :=
  fun q hq => h q (hsub.mem hq)

/-- The converse, which is the direction that needs the duplicate: if every pair
    in `l'` agrees, and every pair of `l` already occurs in `l'`, then every pair
    of `l` agrees. Deduplication produces exactly such an `l'`. -/
theorem all_eq_of_mem_of_all_eq {p : Nat} {l l' : List (ZMod p × ZMod p)}
    (hcover : ∀ q ∈ l, q ∈ l') (h : ∀ q ∈ l', q.1 = q.2) : ∀ q ∈ l, q.1 = q.2 :=
  fun q hq => h q (hcover q hq)

/-- Combining the two: satisfaction is preserved exactly when the surviving
    constraint list is a sublist of the original that still covers it. This is
    the specification `dedupOps` has to meet at the list level. -/
theorem all_eq_iff_of_sublist_of_cover {p : Nat} {l l' : List (ZMod p × ZMod p)}
    (hsub : l'.Sublist l) (hcover : ∀ q ∈ l, q ∈ l') :
    (∀ q ∈ l', q.1 = q.2) ↔ (∀ q ∈ l, q.1 = q.2) :=
  ⟨all_eq_of_mem_of_all_eq hcover, all_eq_of_sublist hsub⟩

/-! ## Piece 2 — how `evalBody` reacts to removing an operation (partly proved)

The composition lemma below is the workhorse: it says `evalBody` distributes
over concatenation, threading the environment and concatenating the constraint
lists. Everything about removing an operation from the middle of a block is
stated against it. -/

/-- `evalBody` composes over concatenation: run the prefix, thread its
    environment into the suffix, concatenate the constraint lists. -/
theorem evalBody_append {p : Nat} (ctx : IRContext OpCode) (l₁ l₂ : List OperationPtr)
    (env : ValEnv p) :
    evalBody ctx (l₁ ++ l₂) env =
      (do
        let (env₁, cs₁) ← evalBody ctx l₁ env
        let (env₂, cs₂) ← evalBody ctx l₂ env₁
        return (env₂, cs₁ ++ cs₂)) := by
  induction l₁ generalizing env with
  | nil => simp [evalBody]
  | cons op rest ih =>
    simp only [List.cons_append, evalBody]
    split
    · cases h1 : env[op.getOperand! ctx 0]? <;> simp
      cases h2 : env[op.getOperand! ctx 1]? <;> simp
      cases h3 : evalBody ctx rest env <;> simp [h3, ih] <;>
        cases h4 : evalBody ctx l₂ (Prod.fst ‹_›) <;> simp
    · cases h5 : evalFeltOp ctx op env <;> simp [ih]

/-- Removing a `constrain.eq` from the middle of a list leaves the environment
    untouched — it defines nothing — and deletes exactly one pair from the
    constraint list.

    Follows from `evalBody_append` by unfolding the `constrain.eq` branch on the
    suffix; the remaining work is bind-reduction bookkeeping. -/
theorem evalBody_erase_middle {p : Nat} (ctx : IRContext OpCode)
    (pre post : List OperationPtr) (op : OperationPtr) (env : ValEnv p)
    (hop : op.getOpType! ctx = .constrain .eq)
    {e : ValEnv p} {c : List (ZMod p × ZMod p)}
    (h : evalBody ctx (pre ++ op :: post) env = some (e, c)) :
    ∃ c₁ a b c₂, c = c₁ ++ (a, b) :: c₂ ∧
      evalBody ctx (pre ++ post) env = some (e, c₁ ++ c₂) := by
  sorry

/-- The pair dropped by `evalBody_erase_middle` is still covered when an earlier
    `constrain.eq` had the same operands. Needs environment monotonicity: once a
    `ValuePtr` is bound, later lookups return the same value, so the earlier
    duplicate contributes an identical pair. -/
theorem dropped_pair_covered {p : Nat} (ctx : IRContext OpCode)
    (pre post : List OperationPtr) (op earlier : OperationPtr) (env : ValEnv p)
    (hop : op.getOpType! ctx = .constrain .eq)
    (hearlier : earlier ∈ pre)
    (hkey : key? ctx earlier = key? ctx op)
    {e : ValEnv p} {c₁ : List (ZMod p × ZMod p)} {a b : ZMod p}
    {c₂ : List (ZMod p × ZMod p)}
    (h : evalBody ctx (pre ++ op :: post) env = some (e, c₁ ++ (a, b) :: c₂)) :
    (a, b) ∈ c₁ ++ c₂ := by
  sorry

/-! ## Piece 1 — the IR-level list lemma (open)

How `opsOf` changes under `WfRewriter.eraseOp`. The op-chain lemmas needed are
all proved already in `Veir/Rewriter/WfRewriter/GetSet.lean` —
`BlockPtr.firstOp!_wfRewriter_eraseOp`, `OperationPtr.next!_wfRewriter_eraseOp` —
so this is an induction on `op_chain.eq_1` that patches the chain across the
removed link, in the same shape as `op_chain_eq_drop`. -/

theorem opsOf_eraseOp {ctx : WfIRContext OpCode} {blk : BlockPtr} {op : OperationPtr}
    (hblk : blk.InBounds ctx.raw) (hop : op.InBounds ctx.raw)
    (hRegions : op.getNumRegions! ctx.raw = 0) (hUses : !op.hasUses! ctx.raw)
    (hParent : (op.get! ctx.raw).parent = some blk) :
    Semantics.opsOf (WfRewriter.eraseOp ctx op hRegions hUses hop) blk (by sorry)
      = (Semantics.opsOf ctx blk hblk).erase op := by
  sorry

/-! ## The theorem

With pieces 1 and 2 in place this is bookkeeping: rewrite `IRSat` through
`irsatb_iff_IRSat`'s bridge to get both sides over the same shape, apply piece 1
to relate the op lists, piece 2 to relate the constraint lists, and piece 3 to
conclude. The `cover` hypothesis piece 3 needs is precisely the invariant
`dedupOps` maintains: it only erases an operation whose key is already in `seen`,
and every key in `seen` was put there by an operation it did not erase. -/

theorem irsat_dedupBlock {p : Nat} (ctx : WfIRContext OpCode) (blk : BlockPtr)
    (hblk : blk.InBounds ctx.raw) (σ : Assignment p) :
    IRSat (dedupBlock ctx blk hblk) blk (by sorry) σ ↔ IRSat ctx blk hblk σ := by
  sorry

end

end DedupConstraints
end LLZK
end Veir
