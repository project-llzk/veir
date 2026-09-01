module

public import Veir.Pass
public import Veir.Dialects.LLZK.Semantics.Constraint
import Veir.Rewriter.WfRewriter

/-!
# Constraint deduplication for LLZK

Removes a `constrain.eq` whose operand pair has already been asserted earlier in
the same block. Asserting `a = b` twice constrains nothing that asserting it once
does not, so the constraint system is unchanged — that is
`irsat_dedupBlock` in `Veir/Passes/LLZK/DedupConstraintsProofs.lean`.

Not a `LocalRewritePattern`: the match depends on *earlier* operations, so this
is a stateful walk, modelled on `Veir/Passes/CSE.lean`.

CSE does not already do this. `constrain.eq` declares `getEffects := .write` —
deliberately, so that DCE cannot delete the constraint system — and CSE only
considers memory-independent operations.

**Block-local by design.** Duplicates are only removed within a single block,
which is exactly the scope `IRSat` is stated over. Cross-block deduplication
would need dominance and a correspondingly bigger theorem.
-/

namespace Veir
namespace LLZK
namespace DedupConstraints

public section

/-- What makes two `constrain.eq` operations duplicates: the same operand pair,
    in the same order.

    Order-sensitive on purpose. `constrain.eq(a, b)` and `constrain.eq(b, a)`
    do assert the same thing, so treating the pair as unordered would be sound
    (`a = b ↔ b = a`) and would remove strictly more. It is left out here so
    that the pass matches `llzk-opt --llzk-duplicate-op-elim` exactly, which
    keeps the differential test meaningful. -/
structure Key where
  lhs : ValuePtr
  rhs : ValuePtr
deriving DecidableEq, BEq, Hashable

/-- `some key` when `op` is a `constrain.eq`, `none` otherwise. -/
def key? (ctx : IRContext OpCode) (op : OperationPtr) : Option Key :=
  match op.getOpType! ctx with
  | .constrain .eq => some { lhs := op.getOperand! ctx 0, rhs := op.getOperand! ctx 1 }
  | _ => none

/-- Deduplicate a *list* of operations, keeping the first occurrence of each
    operand pair and erasing later repeats.

    Takes the list rather than the block, and recurses structurally, for the
    same reason `evalBody` does: a `while` walk compiles to `forIn` over `Loop`
    and yields no equation lemmas, so any theorem about it is unprovable. This
    shape gives `dedupOps.eq_1`/`eq_2`, which the correctness proof rewrites
    with. All the opacity stays in the single choice of which list is passed in.

    Erasing is safe on a pre-computed list: `Rewriter.eraseOp_inBounds` says a
    pointer that does not reference the erased operation stays in bounds, and
    `constrain.eq` has 2 operands, 0 results and 0 regions
    (`Constrain.verifyLocalInvariants`), so it has no uses and nothing needs
    rewiring. -/
def dedupOps (ctx : WfIRContext OpCode) (ops : List OperationPtr)
    (seen : Std.HashSet Key) : WfIRContext OpCode :=
  match ops with
  | [] => ctx
  | op :: rest =>
    match key? ctx.raw op with
    | none => dedupOps ctx rest seen
    | some k =>
      if seen.contains k then
        dedupOps (WfRewriter.eraseOp! ctx op) rest seen
      else
        dedupOps ctx rest (seen.insert k)

/-- Deduplicate the `constrain.eq` operations of a single block. -/
def dedupBlock (ctx : WfIRContext OpCode) (blk : BlockPtr)
    (hblk : blk.InBounds ctx.raw := by grind) : WfIRContext OpCode :=
  dedupOps ctx (Semantics.opsOf ctx blk hblk) ∅

/-- Every block nested anywhere under `op`.

    Safe to compute once up front: this pass only erases `constrain.eq`, which
    has zero regions, so no block is ever invalidated by the rewriting below. -/
partial def blocksUnder (ctx : IRContext OpCode) (op : OperationPtr) : Array BlockPtr := Id.run do
  let mut acc : Array BlockPtr := #[]
  for region in (op.get! ctx).regions do
    let mut b := (region.get! ctx).firstBlock
    while let some blk := b do
      acc := acc.push blk
      let mut o := (blk.get! ctx).firstOp
      while let some inner := o do
        acc := acc ++ blocksUnder ctx inner
        o := (inner.get! ctx).next
      b := (blk.get! ctx).next
  return acc

/-- Run deduplication over every block under `top`. -/
def run (ctx : WfIRContext OpCode) (top : OperationPtr) : WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  for blk in blocksUnder ctx.raw top do
    if h : blk.InBounds ctx.raw then
      ctx := dedupBlock ctx blk h
  return ctx

def impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) :=
  pure (run ctx op)

end

end DedupConstraints

public def DedupConstraintsPass : Pass OpCode :=
  { name := "llzk-dedup-constraints"
    description := "Remove `constrain.eq` operations that repeat an earlier assertion in the same block."
    run := fun _ => DedupConstraints.impl }

end LLZK
end Veir
