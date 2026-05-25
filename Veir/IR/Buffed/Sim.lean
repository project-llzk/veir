module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Layout
public import Veir.Prelude

open Veir.Buffed

-- TODO: Move in prelude?
instance : HAdd Nat (Std.Rco Int) (Std.Rco Nat) where
  hAdd x y := (x + y.lower).toNat...(x + y.upper).toNat

namespace Veir

variable [HasOpInfo OpInfo]

/-! ## Translate a high-level pointer to a flat address. -/

def OperationPtr.toFlat (ptr : OperationPtr) := ptr.id

def BlockPtr.toFlat (ptr : BlockPtr) := ptr.id

def RegionPtr.toFlat (ptr : RegionPtr) := ptr.id

def OpResultPtr.toFlat (ptr : OpResultPtr) (ctx : IRContext OpInfo) :=
  (Int.ofNat ptr.op.toFlat + (Buffed.Operation.Offsets.results (ptr.op.get! ctx)).toInt).toNat +
  ptr.index * Buffed.OpResult.size.toNat

def OpOperandPtr.toFlat (ptr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  (Int.ofNat ptr.op.toFlat + (Buffed.Operation.Offsets.operands (ptr.op.get! ctx)).toInt).toNat +
  ptr.index * Buffed.OpOperand.size.toNat

def BlockOperandPtr.toFlat (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  (Int.ofNat ptr.op.toFlat + (Buffed.Operation.Offsets.blockOperands (ptr.op.get! ctx)).toInt).toNat +
  ptr.index * Buffed.BlockOperand.size.toNat

def BlockArgumentPtr.toFlat (ptr : BlockArgumentPtr) :=
  (Int.ofNat ptr.block.toFlat + Buffed.Block.Offsets.arguments.toInt).toNat +
  ptr.index * Buffed.BlockArgument.size.toNat

def ValuePtr.toFlat (ptr : ValuePtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .opResult ptr => ptr.toFlat ctx
  | .blockArgument ptr => ptr.toFlat

def OpOperandPtrPtr.toFlat (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse ptr => ptr.toFlat ctx
  | .valueFirstUse ptr => ptr.toFlat ctx

def BlockOperandPtrPtr.toFlat (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse ptr => ptr.toFlat ctx
  | .blockFirstUse ptr => ptr.toFlat

/-! ## A pointer is representable if it fits in 63 bits. -/

@[grind] def OperationPtr.IsRepr (ptr : OperationPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind] def BlockPtr.IsRepr (ptr : BlockPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind] def RegionPtr.IsRepr (ptr : RegionPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind] def OpResultPtr.IsRepr (ctx : IRContext OpInfo) (ptr : OpResultPtr) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind] def OpOperandPtr.IsRepr (ctx : IRContext OpInfo) (ptr : OpOperandPtr) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind] def BlockOperandPtr.IsRepr (ctx : IRContext OpInfo) (ptr : BlockOperandPtr) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind] def BlockArgumentPtr.IsRepr (ptr : BlockArgumentPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind] def ValuePtr.IsRepr (ctx : IRContext OpInfo) (ptr : ValuePtr) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind] def OpOperandPtrPtr.IsRepr (ctx : IRContext OpInfo) (ptr : OpOperandPtrPtr) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind] def BlockOperandPtrPtr.IsRepr (ctx : IRContext OpInfo) (ptr : BlockOperandPtrPtr) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

/-! ## Translate a high-level pointer to a buffed address. -/

def OperationPtr.toM (ptr : OperationPtr) : OperationMPtr := ptr.id.toUInt64
def OperationPtr.toO (ptr : Option OperationPtr) : OperationOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

def BlockPtr.toM (ptr : BlockPtr) : BlockMPtr := ptr.id.toUInt64
def BlockPtr.toO (ptr : Option BlockPtr) : BlockOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

def RegionPtr.toM (ptr : RegionPtr) : RegionMPtr := ptr.id.toUInt64
def RegionPtr.toO (ptr : Option RegionPtr) : RegionOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

def OpResultPtr.toM (ptr : OpResultPtr) (ctx : IRContext OpInfo) : OpResultMPtr :=
  (ptr.toFlat ctx).toUInt64
def OpResultPtr.toO (ptr : Option OpResultPtr) (ctx : IRContext OpInfo) : OpResultOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

def BlockArgumentPtr.toM (ptr : BlockArgumentPtr) : BlockArgumentMPtr :=
  ptr.toFlat.toUInt64
def BlockArgumentPtr.toO (ptr : Option BlockArgumentPtr) : BlockArgumentOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

def OpOperandPtr.toM (ptr : OpOperandPtr) (ctx : IRContext OpInfo) : OpOperandMPtr :=
  (ptr.toFlat ctx).toUInt64
def OpOperandPtr.toO (ptr : Option OpOperandPtr) (ctx : IRContext OpInfo) : OpOperandOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

def BlockOperandPtr.toM (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) : BlockOperandMPtr :=
  (ptr.toFlat ctx).toUInt64
def BlockOperandPtr.toO (ptr : Option BlockOperandPtr) (ctx : IRContext OpInfo) : BlockOperandOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

def ValuePtr.toM (ptr : ValuePtr) (ctx : IRContext OpInfo) : ValueImplMPtr :=
  (ptr.toFlat ctx).toUInt64
def ValuePtr.toO (ptr : Option ValuePtr) (ctx : IRContext OpInfo) : ValueImplOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

def OpOperandPtrPtr.toM (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) : GenericMPtr :=
  (ptr.toFlat ctx).toUInt64

def BlockOperandPtrPtr.toM (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) : GenericMPtr :=
  (ptr.toFlat ctx).toUInt64

def GenericPtr.toM (ptr : GenericPtr) (ctx : IRContext OpInfo) : GenericMPtr :=
  match ptr with
  | .operation ptr => ptr.toM
  | .block ptr => ptr.toM
  | .region ptr => ptr.toM
  | .opResult ptr => ptr.toM ctx
  | .blockArgument ptr => ptr.toM
  | .opOperand ptr => ptr.toM ctx
  | .blockOperand ptr => ptr.toM ctx
  | .blockOperandPtr ptr => ptr.toM ctx
  | .value ptr => ptr.toM ctx
  | .opOperandPtr ptr => ptr.toM ctx

/-! ## Range of a pointer -/

def OperationPtr.range (op : OperationPtr) (ctx : IRContext OpInfo) :=
  op.toFlat + (Buffed.Operation.range op ctx)

def BlockPtr.range (bl : BlockPtr) (ctx : IRContext OpInfo) :=
  bl.toFlat + Buffed.Block.range bl ctx

def RegionPtr.range (rg : RegionPtr) :=
  rg.toFlat + Buffed.Region.range

def OpResultPtr.range (res : OpResultPtr) (ctx : IRContext OpInfo) :=
  res.toFlat ctx + Buffed.OpResult.range

def BlockArgumentPtr.range (arg : BlockArgumentPtr) :=
  arg.toFlat + Buffed.BlockArgument.range

def OpOperandPtr.range (opr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlat ctx + Buffed.OpOperand.range

def BlockOperandPtr.range (opr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlat ctx + Buffed.BlockOperand.range

def ValuePtr.range (val : ValuePtr) (ctx : IRContext OpInfo) :=
  match val with
  | .opResult res => res.range ctx
  | .blockArgument arg => arg.range

def OpOperandPtrPtr.range (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse opr => opr.range ctx
  | .valueFirstUse val => val.range ctx

def BlockOperandPtrPtr.range (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse opr => opr.range ctx
  | .blockFirstUse bl => bl.range ctx

def GenericPtr.range (ptr : GenericPtr) (ctx : IRContext OpInfo) : Std.Rco Nat :=
  match ptr with
  | .operation op => op.range ctx
  | .block bl => bl.range ctx
  | .region rg => rg.range
  | .opResult res => res.range ctx
  | .opOperand opr => opr.range ctx
  | .blockOperand opr => opr.range ctx
  | .blockOperandPtr ptr => ptr.range ctx
  | .blockArgument arg => arg.range
  | .value val => val.range ctx
  | .opOperandPtr ptr => ptr.range ctx

/-! ## An object is representable if all its fields are representable. -/

@[grind]
structure ValueImpl.IsRepr (val : ValueImpl) (ctx : IRContext OpInfo) where
  firstUse : val.firstUse.maybe₁ (OpOperandPtr.IsRepr ctx)

@[grind]
structure OpResult.IsRepr (val : OpResult) (ctx : IRContext OpInfo) where
  valueImpl : val.toValueImpl.IsRepr ctx
  index : val.index ≤ UInt32.size
  owner : val.owner.IsRepr

@[grind]
structure BlockArgument.IsRepr (val : BlockArgument) (ctx : IRContext OpInfo) where
  valueImpl : val.toValueImpl.IsRepr ctx
  index : val.index ≤ UInt32.size
  owner : val.owner.IsRepr

@[grind]
structure OpOperand.IsRepr (val : OpOperand) (ctx : IRContext OpInfo) where
  nextUse : val.nextUse.maybe₁ (OpOperandPtr.IsRepr ctx)
  back : val.back.IsRepr ctx
  owner : val.owner.IsRepr
  value : val.owner.IsRepr

@[grind]
structure BlockOperand.IsRepr (val : BlockOperand) (ctx : IRContext OpInfo) where
  nextUse : val.nextUse.maybe₁ (BlockOperandPtr.IsRepr ctx)
  back : val.back.IsRepr ctx
  owner : val.owner.IsRepr
  value : val.owner.IsRepr

@[grind]
structure Operation.IsRepr (val : Operation OpInfo) (ctx : IRContext OpInfo) where
  results : ∀ res ∈ val.results, res.IsRepr ctx
  prev : val.prev.maybe₁ OperationPtr.IsRepr
  next : val.next.maybe₁ OperationPtr.IsRepr
  parent : val.parent.maybe₁ BlockPtr.IsRepr
  blockOperands : ∀ bo ∈ val.blockOperands, bo.IsRepr ctx
  regions : ∀ rg ∈ val.blockOperands, rg.IsRepr ctx
  operands : ∀ operand ∈ val.blockOperands, operand.IsRepr ctx

@[grind]
structure Block.IsRepr (val : Block) (ctx : IRContext OpInfo) where
  firstUse : val.firstUse.maybe₁ (BlockOperandPtr.IsRepr ctx)
  prev : val.prev.maybe₁ BlockPtr.IsRepr
  next : val.next.maybe₁ BlockPtr.IsRepr
  parent : val.parent.maybe₁ RegionPtr.IsRepr
  firstOp : val.firstOp.maybe₁ OperationPtr.IsRepr
  lastOp : val.lastOp.maybe₁ OperationPtr.IsRepr
  arguments : ∀ ba ∈ val.arguments, ba.IsRepr ctx

@[grind]
structure Region.IsRepr (val : Region) (ctx : IRContext OpInfo) where
  firstBlock : val.firstBlock.maybe₁ BlockPtr.IsRepr
  lastBlock : val.lastBlock.maybe₁ BlockPtr.IsRepr
  parent : val.parent.maybe₁ OperationPtr.IsRepr

@[grind]
structure IRContext.IsRepr (ctx : IRContext OpInfo) where
  operations op (hin : op ∈ ctx.operations) : (op.get! ctx).IsRepr ctx
  blocks blk (hin : blk ∈ ctx.blocks) : (blk.get! ctx).IsRepr ctx
  regions rg (hin : rg ∈ ctx.regions) : (rg.get! ctx).IsRepr ctx

/-! ## Refinement predicate. -/

structure OpResultPtr.Matches (ctx : IRContext OpInfo) (bctx : IRBufContext OpInfo) (res : OpResultPtr) where
  ptr_repr : res.IsRepr ctx
  obj_repr : (res.get! ctx).IsRepr ctx
  type : bctx.attributes[(res.toM ctx).readType! bctx]? = some (res.get! ctx).type
  firstUse : OpOperandPtr.toO (res.get! ctx).firstUse ctx = (res.toM ctx).readFirstUse! bctx
  index : (res.get! ctx).index = ((res.toM ctx).readIndex! bctx).toNat
  owner : (res.get! ctx).owner.toM = (res.toM ctx).readOwner! bctx

structure BlockOperandPtr.Matches (ctx : IRContext OpInfo) (bctx : IRBufContext OpInfo) (res : BlockOperandPtr) where
  ptr_repr : res.IsRepr ctx
  obj_repr : (res.get! ctx).IsRepr ctx
  nextUse : BlockOperandPtr.toO (res.get! ctx).nextUse ctx = BlockOperandMPtr.readNextUse! bctx (res.toM ctx)
  back : ((res.get! ctx).back.toFlat ctx).toUInt64 = BlockOperandMPtr.readBack! bctx (res.toM ctx)
  owner : (res.get! ctx).owner.toM = BlockOperandMPtr.readOwner! bctx (res.toM ctx)
  value : (res.get! ctx).value.toM = BlockOperandMPtr.readValue! bctx (res.toM ctx)

structure BlockArgumentPtr.Matches (ctx : IRContext OpInfo) (bctx : IRBufContext OpInfo) (arg : BlockArgumentPtr) where
  ptr_repr : arg.IsRepr
  obj_repr : (arg.get! ctx).IsRepr ctx
  type : bctx.attributes[arg.toM.readType! bctx]? = some (arg.get! ctx).type
  firstUse : OpOperandPtr.toO (arg.get! ctx).firstUse ctx = arg.toM.readFirstUse! bctx
  index : (arg.get! ctx).index = (arg.toM.readIndex! bctx).toNat
  owner : (arg.get! ctx).owner.toM = arg.toM.readOwner! bctx
  -- `loc` is not implemented yet

structure BlockPtr.Matches (ctx : IRContext OpInfo) (bctx : IRBufContext OpInfo) (res : BlockPtr) where
  ptr_repr : res.IsRepr
  obj_repr : (res.get! ctx).IsRepr ctx
  firstUse : BlockOperandPtr.toO (res.get! ctx).firstUse ctx = BlockMPtr.readFirstUse! bctx (res.toM)
  prev : BlockPtr.toO (res.get! ctx).prev = BlockMPtr.readPrev! bctx (res.toM)
  next : BlockPtr.toO (res.get! ctx).next = BlockMPtr.readNext! bctx (res.toM)
  parent : RegionPtr.toO (res.get! ctx).parent = BlockMPtr.readParent! bctx (res.toM)
  firstOp : OperationPtr.toO (res.get! ctx).firstOp = BlockMPtr.readFirstOp! bctx (res.toM)
  lastOp : OperationPtr.toO (res.get! ctx).lastOp = BlockMPtr.readLastOp! bctx (res.toM)
  numArguments : (res.get! ctx).arguments.size = (BlockMPtr.readNumArguments! bctx (res.toM)).toNat
  arguments idx (hidx : idx < (res.getNumArguments! ctx)) : (res.getArgument idx).Matches ctx bctx

structure OpOperandPtr.Matches (ctx : IRContext OpInfo) (bctx : IRBufContext OpInfo) (res : OpOperandPtr) where
  ptr_repr : res.IsRepr ctx
  obj_repr : (res.get! ctx).IsRepr ctx
  nextUse : OpOperandPtr.toO (res.get! ctx).nextUse ctx = OpOperandMPtr.readNextUse! bctx (res.toM ctx)
  back : ((res.get! ctx).back.toFlat ctx).toUInt64 = OpOperandMPtr.readBack! bctx (res.toM ctx)
  owner : (res.get! ctx).owner.toM = OpOperandMPtr.readOwner! bctx (res.toM ctx)
  value : (res.get! ctx).value.toM ctx = OpOperandMPtr.readValue! bctx (res.toM ctx)

structure RegionPtr.Matches (ctx : IRContext OpInfo) (bctx : IRBufContext OpInfo) (reg : RegionPtr) where
  ptr_repr : reg.IsRepr
  obj_repr : (reg.get! ctx).IsRepr ctx
  firstBlock : BlockPtr.toO (reg.get! ctx).firstBlock = RegionMPtr.readFirstBlock! bctx (reg.toM)
  lastBlock : BlockPtr.toO (reg.get! ctx).lastBlock = RegionMPtr.readLastBlock! bctx (reg.toM)
  parent : OperationPtr.toO (reg.get! ctx).parent = RegionMPtr.readParent! bctx (reg.toM)

structure OperationPtr.Matches (ctx : IRContext OpInfo) (bctx : IRBufContext OpInfo) (op : OperationPtr) where
  ptr_repr : op.IsRepr
  obj_repr : (op.get! ctx).IsRepr ctx
  results res (hin : res ∈ (op.getOpResults! ctx)) : res.Matches ctx bctx
  prev : OperationPtr.toO (op.get! ctx).prev = op.toM.readPrev! bctx
  next : OperationPtr.toO (op.get! ctx).next = op.toM.readNext! bctx
  parent : BlockPtr.toO (op.get! ctx).parent = op.toM.readParent! bctx
  opType : (op.get! ctx).opType = Operation.decodeOpInfo (op.toM.readOpType! bctx)
  attrs : bctx.attributes[op.toM.readAttrs! bctx]? = some (op.get! ctx).attrs
  -- TODO: properties
  numBlockOperands : op.getNumSuccessors! ctx = (op.toM.readNumBlockOperands! bctx).toNat
  blockOperands bo (hin : bo ∈ (op.getSuccessors! ctx)) : bo.Matches ctx bctx
  numRegions : op.getNumRegions! ctx = (op.toM.readNumRegions! bctx).toNat
  regions idx (hidx : idx < (op.getNumRegions! ctx)) : (op.getRegion! ctx idx).Matches ctx bctx
  numOperands : op.getNumOperands! ctx = (op.toM.readNumOperands! bctx).toNat
  operands idx (hidx : idx < (op.getNumOperands! ctx)) : (op.getOpOperand idx).Matches ctx bctx

def GenericPtr.MayOverlap (ptr₁ ptr₂ : GenericPtr) : Prop :=
  match ptr₁, ptr₂ with
  | .operation ptr₁, .opOperand ptr₂ => ptr₁ = ptr₂.op
  | .opOperand ptr₁, .operation ptr₂ => ptr₁.op = ptr₂
  | .operation ptr₁, .opResult ptr₂ => ptr₁ = ptr₂.op
  | .opResult ptr₁, .operation ptr₂ => ptr₁.op = ptr₂
  | .blockOperand ptr₁, .operation ptr₂ => ptr₁.op = ptr₂
  | .operation ptr₁, .blockOperand ptr₂ => ptr₁ = ptr₂.op
  | .block ptr₁, .blockArgument ptr₂ => ptr₁ = ptr₂.block
  | .blockArgument ptr₁, .block ptr₂ => ptr₁.block = ptr₂
  | _, _ => False

@[grind]
structure Sim (bctx : IRBufContext OpInfo) (ctx : IRContext OpInfo) where
  /-- All the values are representable. -/
  repr : ctx.IsRepr
  /-- Allocated addresses do not go beyond the buffer size. -/
  in_bounds (ptr : GenericPtr) (ib : ptr.InBounds ctx) :
    IsIncluded (ptr.range ctx) bctx.mem.range
  /-- The allocations are disjoint. -/
  disjoint_allocs (ptr₁ ptr₂ : GenericPtr) (ib₁ : ptr₁.InBounds ctx) (ib₂ : ptr₂.InBounds ctx)
      (h : ¬ ptr₁.MayOverlap ptr₂) (hneq : ptr₁ ≠ ptr₂) :
    IsDisjoint (ptr₁.range ctx) (ptr₂.range ctx)
  /-- The buffer contains the encodings of all the operations. -/
  encoding_op (op : OperationPtr) (ib : op.InBounds ctx) :
    op.Matches ctx bctx
  /-- The buffer contains the encodings of all the blocks. -/
  encoding_block (blk : BlockPtr) (ib : blk.InBounds ctx) :
    blk.Matches ctx bctx
  /-- The buffer contains the encodings of all the regions. -/
  encoding_region (rg : RegionPtr) (ib : rg.InBounds ctx) :
    rg.Matches ctx bctx

structure Sim.IRContext where
  buf : IRBufContext OpInfo
  ctx : Veir.IRContext OpInfo
  sim : Sim buf ctx
