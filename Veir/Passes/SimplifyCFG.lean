import Veir.Pass
import Veir.Rewriter.WfRewriter

/-!
  # SimplifyCFG

  A pass that simplifies the control flow graph. Currently it implements
  a single transformation: remove basic blocks that are unreachable from
  the entry block of their containing region.

  Reachability is computed per region by BFS from `region.firstBlock`,
  following each block's terminator successors (the block operands of
  its last operation).
-/

namespace Veir
namespace SimplifyCFG

/-- Walk a region's block linked list and collect every block it owns. -/
def blocksInRegion (ctx : IRContext OpCode) (region : RegionPtr) :
    Array BlockPtr := Id.run do
  let mut result : Array BlockPtr := #[]
  let mut cur := (region.get! ctx).firstBlock
  while h : cur.isSome do
    let blk := cur.get h
    result := result.push blk
    cur := (blk.get! ctx).next
  return result

/-- The successor blocks of `block`'s terminator (its last operation).
    Returns an empty array if the block is empty or its terminator has
    no successors. -/
def successorsOf (ctx : IRContext OpCode) (block : BlockPtr) :
    Array BlockPtr :=
  match (block.get! ctx).lastOp with
  | none => #[]
  | some term => term.getSuccessors! ctx

/-- Set of blocks reachable from `region`'s entry via terminator
    successors. -/
def reachableBlocks (ctx : IRContext OpCode) (region : RegionPtr) :
    Std.HashSet BlockPtr := Id.run do
  let mut visited : Std.HashSet BlockPtr := Std.HashSet.emptyWithCapacity
  let some entry := (region.get! ctx).firstBlock | return visited
  let mut stack : Array BlockPtr := #[entry]
  while h : stack.size > 0 do
    let blk := stack[stack.size - 1]
    stack := stack.pop
    if visited.contains blk then
      continue
    visited := visited.insert blk
    for succ in successorsOf ctx blk do
      unless visited.contains succ do
        stack := stack.push succ
  return visited

set_option warn.sorry false in
/-- Erase every operation contained in `block`, leaving the block
    structurally empty (but still linked into its region). -/
def eraseOpsInBlock (ctx : WfIRContext OpCode) (block : BlockPtr) :
    WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  while h : ((block.get! ctx.raw).lastOp).isSome do
    let op := ((block.get! ctx.raw).lastOp).get h
    ctx := WfRewriter.eraseOp ctx op sorry sorry sorry
  return ctx

set_option warn.sorry false in
/-- Unlink `block` from its region's block linked list and remove it
    from the IR context. The caller is responsible for ensuring nothing
    in the surviving IR references `block` (e.g., this is only called
    on blocks proved unreachable, after their contents have been
    erased). -/
def deallocBlock (ctx : WfIRContext OpCode) (block : BlockPtr) :
    WfIRContext OpCode :=
  let raw := ctx.raw
  let blk := block.get! raw
  let raw :=
    match blk.parent with
    | none => raw
    | some region =>
      let reg := region.get! raw
      let raw :=
        if reg.firstBlock = some block then
          region.setFirstBlock! raw blk.next
        else raw
      if reg.lastBlock = some block then
        region.setLastBlock! raw blk.prev
      else raw
  let raw :=
    match blk.prev with
    | none => raw
    | some p => p.setNextBlock! raw blk.next
  let raw :=
    match blk.next with
    | none => raw
    | some n => n.setPrevBlock! raw blk.prev
  let raw := { raw with blocks := raw.blocks.erase block }
  ⟨raw, sorry⟩

set_option warn.sorry false in
/-- Remove all blocks in `region` that are not reachable from its
    entry block. Erases their contents first (to break uses, including
    block-operand uses of reachable blocks), then unlinks and
    deallocates the blocks themselves. -/
def removeUnreachableInRegion (ctx : WfIRContext OpCode) (region : RegionPtr) :
    WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  let reachable := reachableBlocks ctx.raw region
  let allBlocks := blocksInRegion ctx.raw region
  for block in allBlocks do
    unless reachable.contains block do
      ctx := eraseOpsInBlock ctx block
  for block in allBlocks do
    unless reachable.contains block do
      ctx := deallocBlock ctx block
  return ctx

set_option warn.sorry false in
def processAllRegions (ctx : WfIRContext OpCode) :
    WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  for region in ctx.raw.regions.keys do
    ctx := removeUnreachableInRegion ctx region
  return ctx

def SimplifyCFGPass.impl (ctx : WfIRContext OpCode) (_op : OperationPtr)
    (_ : _op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  pure (SimplifyCFG.processAllRegions ctx)

end SimplifyCFG

public def SimplifyCFGPass : Pass OpCode :=
  { name := "simplify-cfg"
    description :=
      "Simplify the control-flow graph. Currently removes basic blocks " ++
      "that are unreachable from the entry block of their region."
    run := SimplifyCFG.SimplifyCFGPass.impl }

end Veir
