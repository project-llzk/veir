module

public import Veir.IR.Buffed.Layout
public import ExArray.Basic

-- TODO: move
abbrev _root_.UInt64.toInt (x : UInt64) := Int.ofNat x.toNat
abbrev _root_.UInt32.toInt64 (x : UInt32) : Int64 := .ofUInt64 x.toUInt64

attribute [grind =] UInt32.toNat_toUInt64
attribute [local grind! .] UInt64.toNat_lt

namespace Veir.Buffed

/-! ## Low-level pointers.
The `MPtr` point to objects, whereas `OPtr` are nullable, with sentinel value `-1`. -/

abbrev ValueImplMPtr := UInt64
abbrev ValueImplOPtr := UInt64

abbrev OpResultMPtr := UInt64
abbrev OpResultOPtr := UInt64

abbrev BlockArgumentMPtr := UInt64
abbrev BlockArgumentOPtr := UInt64

abbrev OpOperandMPtr := UInt64
abbrev OpOperandOPtr := UInt64

abbrev BlockOperandMPtr := UInt64
abbrev BlockOperandOPtr := UInt64

abbrev OperationMPtr := UInt64
abbrev OperationOPtr := UInt64

abbrev BlockMPtr := UInt64
abbrev BlockOPtr := UInt64

abbrev RegionMPtr := UInt64
abbrev RegionOPtr := UInt64

structure IRContext OpInfo [HasOpInfo OpInfo] where
  mem : ExArray

/-! ## Raw accessors -/

variable [HasOpInfo OpInfo] (bctx : IRContext OpInfo)

@[grind, inline]
def IRContext.size (bctx : IRContext OpInfo) : Nat := bctx.mem.size

@[grind, inline]
def IRContext.usize (bctx : IRContext OpInfo) : UInt64 := bctx.mem.usize

/-! ## Raw accessors for `ValueImpl` -/

def ValueImplMPtr.readType (ptr : ValueImplMPtr) (h : ptr.toNat + ValueImpl.Sizes.type.toNat ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 ptr (by grind)

def ValueImplMPtr.readType! (ptr : ValueImplMPtr) : UInt64 :=
  bctx.mem.read64! ptr

@[simp, grind =]
theorem ValueImplMPtr.readType_eq_readType! {ptr : ValueImplMPtr} {h} :
    ptr.readType bctx h = ptr.readType! bctx := by
  simp [ValueImplMPtr.readType, ValueImplMPtr.readType!]

def ValueImplMPtr.readFirstUse (ptr : ValueImplMPtr)
    (h : (ptr + ValueImpl.Offsets.firstUse).toInt + ValueImpl.Sizes.firstUse.toInt ≤ bctx.size) : OpOperandOPtr :=
  bctx.mem.read64 (ptr + ValueImpl.Offsets.firstUse) (by grind)

def ValueImplMPtr.readFirstUse! (ptr : ValueImplMPtr) : OpOperandOPtr :=
  bctx.mem.read64! (ptr + ValueImpl.Offsets.firstUse)

@[simp, grind =]
theorem ValueImplMPtr.readFirstUse_eq_readFirstUse! {ptr : ValueImplMPtr} {h} :
    ptr.readFirstUse bctx h = ptr.readFirstUse! bctx := by
  simp [ValueImplMPtr.readFirstUse, ValueImplMPtr.readFirstUse!]

/-! ## Raw accessors for `OpResult` -/

def OpResultMPtr.readType (ptr : OpResultMPtr)
    (h : ptr.toNat + ValueImpl.Sizes.type.toNat ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 ptr (by grind)

def OpResultMPtr.readType! (ptr : OpResultMPtr) : UInt64 :=
  bctx.mem.read64! ptr

@[simp, grind =]
theorem OpResultMPtr.readType_eq_readType! {ptr : OpResultMPtr} {h} :
    ptr.readType bctx h = ptr.readType! bctx := by
  simp [OpResultMPtr.readType, OpResultMPtr.readType!]

def OpResultMPtr.readFirstUse (ptr : OpResultMPtr)
    (h : (ptr + ValueImpl.Offsets.firstUse).toInt + ValueImpl.Sizes.firstUse.toInt ≤ bctx.size) : OpOperandOPtr :=
  bctx.mem.read64 (ptr + ValueImpl.Offsets.firstUse) (by grind)

def OpResultMPtr.readFirstUse! (ptr : OpResultMPtr) : OpOperandOPtr :=
  bctx.mem.read64! (ptr + ValueImpl.Offsets.firstUse)

@[simp, grind =]
theorem OpResultMPtr.readFirstUse_eq_readFirstUse! {ptr : OpResultMPtr} {h} :
    ptr.readFirstUse bctx h = ptr.readFirstUse! bctx := by
  simp [OpResultMPtr.readFirstUse, OpResultMPtr.readFirstUse!]

def OpResultMPtr.readIndex (ptr : OpResultMPtr)
    (h : (ptr + OpResult.Offsets.index).toInt + OpResult.Sizes.index.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + OpResult.Offsets.index) (by grind)

def OpResultMPtr.readIndex! (ptr : OpResultMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + OpResult.Offsets.index)

@[simp, grind =]
theorem OpResultMPtr.readIndex_eq_readIndex! {ptr : OpResultMPtr} {h} :
    ptr.readIndex bctx h = ptr.readIndex! bctx := by
  simp [OpResultMPtr.readIndex, OpResultMPtr.readIndex!]

def OpResultMPtr.readOwner (ptr : OpResultMPtr)
    (h : (ptr + OpResult.Offsets.owner).toInt + OpResult.Sizes.owner.toInt ≤ bctx.size) : OperationMPtr :=
  bctx.mem.read64 (ptr + OpResult.Offsets.owner) (by grind)

def OpResultMPtr.readOwner! (ptr : OpResultMPtr) : OperationMPtr :=
  bctx.mem.read64! (ptr + OpResult.Offsets.owner)

@[simp, grind =]
theorem OpResultMPtr.readOwner_eq_readOwner! {ptr : OpResultMPtr} {h} :
    ptr.readOwner bctx h = ptr.readOwner! bctx := by
  simp [OpResultMPtr.readOwner, OpResultMPtr.readOwner!]

/-! ## Raw accessors for `BlockArgument` -/

def BlockArgumentMPtr.readType (ptr : BlockArgumentMPtr)
    (h : ptr.toNat + ValueImpl.Sizes.type.toNat ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 ptr (by grind)

def BlockArgumentMPtr.readType! (ptr : BlockArgumentMPtr) : UInt64 :=
  bctx.mem.read64! ptr

@[simp, grind =]
theorem BlockArgumentMPtr.readType_eq_readType! {ptr : BlockArgumentMPtr} {h} :
    ptr.readType bctx h = ptr.readType! bctx := by
  simp [BlockArgumentMPtr.readType, BlockArgumentMPtr.readType!]

def BlockArgumentMPtr.readFirstUse (ptr : BlockArgumentMPtr)
    (h : (ptr + ValueImpl.Offsets.firstUse).toInt + ValueImpl.Sizes.firstUse.toInt ≤ bctx.size) : OpOperandOPtr :=
  bctx.mem.read64 (ptr + ValueImpl.Offsets.firstUse) (by grind)

def BlockArgumentMPtr.readFirstUse! (ptr : BlockArgumentMPtr) : OpOperandOPtr :=
  bctx.mem.read64! (ptr + ValueImpl.Offsets.firstUse)

@[simp, grind =]
theorem BlockArgumentMPtr.readFirstUse_eq_readFirstUse! {ptr : BlockArgumentMPtr} {h} :
    ptr.readFirstUse bctx h = ptr.readFirstUse! bctx := by
  simp [BlockArgumentMPtr.readFirstUse, BlockArgumentMPtr.readFirstUse!]

def BlockArgumentMPtr.readIndex (ptr : BlockArgumentMPtr)
    (h : (ptr + BlockArgument.Offsets.index).toInt + BlockArgument.Sizes.index.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + BlockArgument.Offsets.index) (by grind)

def BlockArgumentMPtr.readIndex! (ptr : BlockArgumentMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + BlockArgument.Offsets.index)

@[simp, grind =]
theorem BlockArgumentMPtr.readIndex_eq_readIndex! {ptr : BlockArgumentMPtr} {h} :
    ptr.readIndex bctx h = ptr.readIndex! bctx := by
  simp [BlockArgumentMPtr.readIndex, BlockArgumentMPtr.readIndex!]

def BlockArgumentMPtr.readOwner (ptr : BlockArgumentMPtr)
    (h : (ptr + BlockArgument.Offsets.owner).toInt + BlockArgument.Sizes.owner.toInt ≤ bctx.size) : BlockMPtr :=
  bctx.mem.read64 (ptr + BlockArgument.Offsets.owner) (by grind)

def BlockArgumentMPtr.readOwner! (ptr : BlockArgumentMPtr) : BlockMPtr :=
  bctx.mem.read64! (ptr + BlockArgument.Offsets.owner)

@[simp, grind =]
theorem BlockArgumentMPtr.readOwner_eq_readOwner! {ptr : BlockArgumentMPtr} {h} :
    ptr.readOwner bctx h = ptr.readOwner! bctx := by
  simp [BlockArgumentMPtr.readOwner, BlockArgumentMPtr.readOwner!]

/-! ## Raw accessors for `OpOperand` -/

def OpOperandMPtr.readNextUse (ptr : OpOperandMPtr)
    (h : (ptr + OpOperand.Offsets.nextUse).toInt + OpOperand.Sizes.nextUse.toInt ≤ bctx.size) : OpOperandOPtr :=
  bctx.mem.read64 (ptr + OpOperand.Offsets.nextUse) (by grind)

def OpOperandMPtr.readNextUse! (ptr : OpOperandMPtr) : OpOperandOPtr :=
  bctx.mem.read64! (ptr + OpOperand.Offsets.nextUse)

@[simp, grind =]
theorem OpOperandMPtr.readNextUse_eq_readNextUse! {ptr : OpOperandMPtr} {h} :
    ptr.readNextUse bctx h = ptr.readNextUse! bctx := by
  simp [OpOperandMPtr.readNextUse, OpOperandMPtr.readNextUse!]

def OpOperandMPtr.readBack (ptr : OpOperandMPtr)
    (h : (ptr + OpOperand.Offsets.back).toInt + OpOperand.Sizes.back.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + OpOperand.Offsets.back) (by grind)

def OpOperandMPtr.readBack! (ptr : OpOperandMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + OpOperand.Offsets.back)

@[simp, grind =]
theorem OpOperandMPtr.readBack_eq_readBack! {ptr : OpOperandMPtr} {h} :
    ptr.readBack bctx h = ptr.readBack! bctx := by
  simp [OpOperandMPtr.readBack, OpOperandMPtr.readBack!]

def OpOperandMPtr.readOwner (ptr : OpOperandMPtr)
    (h : (ptr + OpOperand.Offsets.owner).toInt + OpOperand.Sizes.owner.toInt ≤ bctx.size) : OperationMPtr :=
  bctx.mem.read64 (ptr + OpOperand.Offsets.owner) (by grind)

def OpOperandMPtr.readOwner! (ptr : OpOperandMPtr) : OperationMPtr :=
  bctx.mem.read64! (ptr + OpOperand.Offsets.owner)

@[simp, grind =]
theorem OpOperandMPtr.readOwner_eq_readOwner! {ptr : OpOperandMPtr} {h} :
    ptr.readOwner bctx h = ptr.readOwner! bctx := by
  simp [OpOperandMPtr.readOwner, OpOperandMPtr.readOwner!]

def OpOperandMPtr.readValue (ptr : OpOperandMPtr)
    (h : (ptr + OpOperand.Offsets.value).toInt + OpOperand.Sizes.value.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + OpOperand.Offsets.value) (by grind)

def OpOperandMPtr.readValue! (ptr : OpOperandMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + OpOperand.Offsets.value)

@[simp, grind =]
theorem OpOperandMPtr.readValue_eq_readValue! {ptr : OpOperandMPtr} {h} :
    ptr.readValue bctx h = ptr.readValue! bctx := by
  simp [OpOperandMPtr.readValue, OpOperandMPtr.readValue!]

/-! ## Raw accessors for `BlockOperand` -/

def BlockOperandMPtr.readNextUse (ptr : BlockOperandMPtr)
    (h : (ptr + BlockOperand.Offsets.nextUse).toInt + BlockOperand.Sizes.nextUse.toInt ≤ bctx.size) : BlockOperandOPtr :=
  bctx.mem.read64 (ptr + BlockOperand.Offsets.nextUse) (by grind)

def BlockOperandMPtr.readNextUse! (ptr : BlockOperandMPtr) : BlockOperandOPtr :=
  bctx.mem.read64! (ptr + BlockOperand.Offsets.nextUse)

@[simp, grind =]
theorem BlockOperandMPtr.readNextUse_eq_readNextUse! {ptr : BlockOperandMPtr} {h} :
    ptr.readNextUse bctx h = ptr.readNextUse! bctx := by
  simp [BlockOperandMPtr.readNextUse, BlockOperandMPtr.readNextUse!]

def BlockOperandMPtr.readBack (ptr : BlockOperandMPtr)
    (h : (ptr + BlockOperand.Offsets.back).toInt + BlockOperand.Sizes.back.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + BlockOperand.Offsets.back) (by grind)

def BlockOperandMPtr.readBack! (ptr : BlockOperandMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + BlockOperand.Offsets.back)

@[simp, grind =]
theorem BlockOperandMPtr.readBack_eq_readBack! {ptr : BlockOperandMPtr} {h} :
    ptr.readBack bctx h = ptr.readBack! bctx := by
  simp [BlockOperandMPtr.readBack, BlockOperandMPtr.readBack!]

def BlockOperandMPtr.readOwner (ptr : BlockOperandMPtr)
    (h : (ptr + BlockOperand.Offsets.owner).toInt + BlockOperand.Sizes.owner.toInt ≤ bctx.size) : OperationMPtr :=
  bctx.mem.read64 (ptr + BlockOperand.Offsets.owner) (by grind)

def BlockOperandMPtr.readOwner! (ptr : BlockOperandMPtr) : OperationMPtr :=
  bctx.mem.read64! (ptr + BlockOperand.Offsets.owner)

@[simp, grind =]
theorem BlockOperandMPtr.readOwner_eq_readOwner! {ptr : BlockOperandMPtr} {h} :
    ptr.readOwner bctx h = ptr.readOwner! bctx := by
  simp [BlockOperandMPtr.readOwner, BlockOperandMPtr.readOwner!]

def BlockOperandMPtr.readValue (ptr : BlockOperandMPtr)
    (h : (ptr + BlockOperand.Offsets.value).toInt + BlockOperand.Sizes.value.toInt ≤ bctx.size) : BlockMPtr :=
  bctx.mem.read64 (ptr + BlockOperand.Offsets.value) (by grind)

def BlockOperandMPtr.readValue! (ptr : BlockOperandMPtr) : BlockMPtr :=
  bctx.mem.read64! (ptr + BlockOperand.Offsets.value)

@[simp, grind =]
theorem BlockOperandMPtr.readValue_eq_readValue! {ptr : BlockOperandMPtr} {h} :
    ptr.readValue bctx h = ptr.readValue! bctx := by
  simp [BlockOperandMPtr.readValue, BlockOperandMPtr.readValue!]

/-! ## Raw accessors for `Operation` -/

def OperationMPtr.readNumResults (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numResults).toInt + Operation.Sizes.numResults.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Operation.Offsets.numResults) (by grind)

def OperationMPtr.readNumResults! (ptr : OperationMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Operation.Offsets.numResults)

@[simp, grind =]
theorem OperationMPtr.readNumResults_eq_readNumResults! {ptr : OperationMPtr} {h} :
    ptr.readNumResults bctx h = ptr.readNumResults! bctx := by
  simp [OperationMPtr.readNumResults, OperationMPtr.readNumResults!]

def OperationMPtr.readPrev (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.prev).toInt + Operation.Sizes.prev.toInt ≤ bctx.size) : OperationOPtr :=
  bctx.mem.read64 (ptr + Operation.Offsets.prev) (by grind)

def OperationMPtr.readPrev! (ptr : OperationMPtr) : OperationOPtr :=
  bctx.mem.read64! (ptr + Operation.Offsets.prev)

@[simp, grind =]
theorem OperationMPtr.readPrev_eq_readPrev! {ptr : OperationMPtr} {h} :
    ptr.readPrev bctx h = ptr.readPrev! bctx := by
  simp [OperationMPtr.readPrev, OperationMPtr.readPrev!]

def OperationMPtr.readNext (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.next).toInt + Operation.Sizes.next.toInt ≤ bctx.size) : OperationOPtr :=
  bctx.mem.read64 (ptr + Operation.Offsets.next) (by grind)

def OperationMPtr.readNext! (ptr : OperationMPtr) : OperationOPtr :=
  bctx.mem.read64! (ptr + Operation.Offsets.next)

@[simp, grind =]
theorem OperationMPtr.readNext_eq_readNext! {ptr : OperationMPtr} {h} :
    ptr.readNext bctx h = ptr.readNext! bctx := by
  simp [OperationMPtr.readNext, OperationMPtr.readNext!]

def OperationMPtr.readParent (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.parent).toInt + Operation.Sizes.parent.toInt ≤ bctx.size) : BlockOPtr :=
  bctx.mem.read64 (ptr + Operation.Offsets.parent) (by grind)

def OperationMPtr.readParent! (ptr : OperationMPtr) : BlockOPtr :=
  bctx.mem.read64! (ptr + Operation.Offsets.parent)

@[simp, grind =]
theorem OperationMPtr.readParent_eq_readParent! {ptr : OperationMPtr} {h} :
    ptr.readParent bctx h = ptr.readParent! bctx := by
  simp [OperationMPtr.readParent, OperationMPtr.readParent!]

def OperationMPtr.readOpType (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤ bctx.size) : UInt32 :=
  bctx.mem.read32 (ptr + Operation.Offsets.opType) (by grind)

def OperationMPtr.readOpType! (ptr : OperationMPtr) : UInt32 :=
  bctx.mem.read32! (ptr + Operation.Offsets.opType)

@[simp, grind =]
theorem OperationMPtr.readOpType_eq_readOpType! {ptr : OperationMPtr} {h} :
    ptr.readOpType bctx h = ptr.readOpType! bctx := by
  simp [OperationMPtr.readOpType, OperationMPtr.readOpType!]

def OperationMPtr.readNumBlockOperands (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numBlockOperands).toInt + Operation.Sizes.numBlockOperands.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Operation.Offsets.numBlockOperands) (by grind)

def OperationMPtr.readNumBlockOperands! (ptr : OperationMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Operation.Offsets.numBlockOperands)

@[simp, grind =]
theorem OperationMPtr.readNumBlockOperands_eq_readNumBlockOperands! {ptr : OperationMPtr} {h} :
    ptr.readNumBlockOperands bctx h = ptr.readNumBlockOperands! bctx := by
  simp [OperationMPtr.readNumBlockOperands, OperationMPtr.readNumBlockOperands!]

def OperationMPtr.readNumRegions (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numRegions).toInt + Operation.Sizes.numRegions.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Operation.Offsets.numRegions) (by grind)

def OperationMPtr.readNumRegions! (ptr : OperationMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Operation.Offsets.numRegions)

@[simp, grind =]
theorem OperationMPtr.readNumRegions_eq_readNumRegions! {ptr : OperationMPtr} {h} :
    ptr.readNumRegions bctx h = ptr.readNumRegions! bctx := by
  simp [OperationMPtr.readNumRegions, OperationMPtr.readNumRegions!]

def OperationMPtr.readNumOperands (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Operation.Offsets.numOperands) (by grind)

def OperationMPtr.readNumOperands! (ptr : OperationMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Operation.Offsets.numOperands)

@[simp, grind =]
theorem OperationMPtr.readNumOperands_eq_readNumOperands! {ptr : OperationMPtr} {h} :
    ptr.readNumOperands bctx h = ptr.readNumOperands! bctx := by
  simp [OperationMPtr.readNumOperands, OperationMPtr.readNumOperands!]

def OperationMPtr.readAttrs (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.attrs).toInt + Operation.Sizes.attrs.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Operation.Offsets.attrs) (by grind)

def OperationMPtr.readAttrs! (ptr : OperationMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Operation.Offsets.attrs)

@[simp, grind =]
theorem OperationMPtr.readAttrs_eq_readAttrs! {ptr : OperationMPtr} {h} :
    ptr.readAttrs bctx h = ptr.readAttrs! bctx := by
  simp [OperationMPtr.readAttrs, OperationMPtr.readAttrs!]

def OperationMPtr.computeOperandsOffset (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤ bctx.size) : Int64 :=
  let prop := ptr.readOpType bctx h
  Operation.Offsets.properties + (Operation.propertySize (OpInfo := OpInfo) (decodeOpInfo prop))

def OperationMPtr.computeOperandsOffset! (ptr : OperationMPtr) : Int64 :=
  let prop := ptr.readOpType! bctx
  Operation.Offsets.properties + (Operation.propertySize (OpInfo := OpInfo) (decodeOpInfo prop))

@[simp, grind =]
theorem OperationMPtr.computeOperandsOffset_eq_computeOperandsOffset! {ptr : OperationMPtr} {h} :
    ptr.computeOperandsOffset bctx h = ptr.computeOperandsOffset! bctx := by
  simp [OperationMPtr.computeOperandsOffset, OperationMPtr.computeOperandsOffset!]

def OperationMPtr.computeOperandOffset (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤ bctx.size) : Int64 :=
  let offset := ptr.computeOperandsOffset bctx h
  offset + (OpOperand.size * idx)

def OperationMPtr.computeOperandOffset! (ptr : OperationMPtr) (idx : UInt64) : Int64 :=
  let offset := ptr.computeOperandsOffset! bctx
  offset + (OpOperand.size * idx)

@[simp, grind =]
theorem OperationMPtr.computeOperandOffset_eq_computeOperandOffset! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.computeOperandOffset bctx idx h = ptr.computeOperandOffset! bctx idx := by
  simp [OperationMPtr.computeOperandOffset, OperationMPtr.computeOperandOffset!]

def OperationMPtr.readNthOperand (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤ bctx.size) : OpOperandMPtr :=
  ptr + ptr.computeOperandOffset bctx idx h

def OperationMPtr.readNthOperand! (ptr : OperationMPtr) (idx : UInt64) : OpOperandMPtr :=
  ptr + ptr.computeOperandOffset! bctx idx

@[simp, grind =]
theorem OperationMPtr.readNthOperand_eq_readNthOperand! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.readNthOperand bctx idx h = ptr.readNthOperand! bctx idx := by
  simp [readNthOperand, readNthOperand!]

def OperationMPtr.computeBlockOperandsOffset (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ bctx.size) : Int64 :=
  have : (Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤
    (Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt := by cbv; constructor
  have : (ptr + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤
    (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt := by sorry
  let offset := ptr.computeOperandsOffset bctx (by grind)
  let count := ptr.readNumOperands bctx (by grind)
  offset + (OpOperand.size * count)

def OperationMPtr.computeBlockOperandsOffset! (ptr : OperationMPtr) : Int64 :=
  let offset := ptr.computeOperandsOffset! bctx
  let count := ptr.readNumOperands! bctx
  offset + (OpOperand.size * count)

@[simp, grind =]
theorem OperationMPtr.computeBlockOperandsOffset_eq_computeBlockOperandsOffset! {ptr : OperationMPtr} {h} :
    ptr.computeBlockOperandsOffset bctx h = ptr.computeBlockOperandsOffset! bctx := by
  simp [computeBlockOperandsOffset!, computeBlockOperandsOffset]

def OperationMPtr.computeBlockOperandOffset (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ bctx.size) : Int64 :=
  let offset := ptr.computeBlockOperandsOffset bctx h
  offset + (BlockOperand.size * idx)

def OperationMPtr.computeBlockOperandOffset! (ptr : OperationMPtr) (idx : UInt64) : Int64 :=
  let offset := ptr.computeBlockOperandsOffset! bctx
  offset + (BlockOperand.size * idx)

@[simp, grind =]
theorem OperationMPtr.computeBlockOperandOffset_eq_computeBlockOperandOffset! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.computeBlockOperandOffset bctx idx h = ptr.computeBlockOperandOffset! bctx idx := by
  simp [computeBlockOperandOffset!, computeBlockOperandOffset]


def OperationMPtr.readNthBlockOperand (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ bctx.size) : BlockOperandMPtr :=
  ptr + ptr.computeBlockOperandOffset bctx idx h

def OperationMPtr.readNthBlockOperand! (ptr : OperationMPtr) (idx : UInt64) : BlockOperandMPtr :=
  ptr + ptr.computeBlockOperandOffset! bctx idx

@[simp, grind =]
theorem OperationMPtr.readNthBlockOperand_eq_readNthBlockOperand! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.readNthBlockOperand bctx idx h = ptr.readNthBlockOperand! bctx idx := by
  simp [readNthBlockOperand!, readNthBlockOperand]

def OperationMPtr.computeRegionsOffset (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numOperands).toInt +
      Operation.Sizes.numOperands.toInt ≤ bctx.size) : Int64 :=
  let offset := ptr.computeBlockOperandsOffset bctx (by grind)
  let count := ptr.readNumBlockOperands bctx (by sorry)
  offset + (BlockOperand.size * count)

def OperationMPtr.computeRegionsOffset! (ptr : OperationMPtr) : Int64 :=
  let offset := ptr.computeBlockOperandsOffset! bctx
  let count := ptr.readNumBlockOperands! bctx
  offset + (BlockOperand.size * count)

@[simp, grind =]
theorem OperationMPtr.computeRegionsOffset_eq_computeRegionsOffset! {ptr : OperationMPtr} {h} :
    ptr.computeRegionsOffset bctx h = ptr.computeRegionsOffset! bctx := by
  simp [computeRegionsOffset!, computeRegionsOffset]

def OperationMPtr.computeRegionOffset (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.numOperands).toInt +
      Operation.Sizes.numOperands.toInt ≤ bctx.size) : Int64 :=
  let offset := ptr.computeRegionsOffset bctx h
  offset + (ptrSize * idx)

def OperationMPtr.computeRegionOffset! (ptr : OperationMPtr) (idx : UInt64) : Int64 :=
  let offset := ptr.computeRegionsOffset! bctx
  offset + (ptrSize * idx)

@[simp, grind =]
theorem OperationMPtr.computeRegionOffset_eq_computeRegionOffset! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.computeRegionOffset bctx idx h = ptr.computeRegionOffset! bctx idx := by
  simp [computeRegionOffset, computeRegionOffset!]

def OperationMPtr.readNthRegion (ptr : OperationMPtr) (idx : UInt64)
    (h₁ : (ptr + Operation.Offsets.numOperands).toInt +
      Operation.Sizes.numOperands.toInt ≤ bctx.size)
    (h₂ : (ptr + ptr.computeRegionOffset bctx idx h₁).toInt + ptrSize.toInt ≤ bctx.size) : RegionMPtr :=
  bctx.mem.read64 (ptr + ptr.computeRegionOffset bctx idx h₁) (by grind)

def OperationMPtr.readNthRegion! (ptr : OperationMPtr) (idx : UInt64) : RegionMPtr :=
  bctx.mem.read64! (ptr + ptr.computeRegionOffset! bctx idx)

@[simp, grind =]
theorem OperationMPtr.readNthRegion_eq_readNthRegion! {ptr : OperationMPtr} {idx : UInt64} {h₁ h₂} :
    ptr.readNthRegion bctx idx h₁ h₂ = ptr.readNthRegion! bctx idx := by
  simp [readNthRegion, readNthRegion!]

/-! ## Raw accessors for `Block` -/

def BlockMPtr.readFirstUse (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.firstUse).toInt + Block.Sizes.firstUse.toInt ≤ bctx.size) : BlockOperandOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.firstUse) (by grind)

def BlockMPtr.readFirstUse! (ptr : BlockMPtr) : BlockOperandOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.firstUse)

@[simp, grind =]
theorem BlockMPtr.readFirstUse_eq_readFirstUse! {ptr : BlockMPtr} {h} :
    ptr.readFirstUse bctx h = ptr.readFirstUse! bctx := by
  simp [BlockMPtr.readFirstUse, BlockMPtr.readFirstUse!]

def BlockMPtr.readPrev (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.prev).toInt + Block.Sizes.prev.toInt ≤ bctx.size) : BlockOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.prev) (by grind)

def BlockMPtr.readPrev! (ptr : BlockMPtr) : BlockOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.prev)

@[simp, grind =]
theorem BlockMPtr.readPrev_eq_readPrev! {ptr : BlockMPtr} {h} :
    ptr.readPrev bctx h = ptr.readPrev! bctx := by
  simp [BlockMPtr.readPrev, BlockMPtr.readPrev!]

def BlockMPtr.readNext (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.next).toInt + Block.Sizes.next.toInt ≤ bctx.size) : BlockOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.next) (by grind)

def BlockMPtr.readNext! (ptr : BlockMPtr) : BlockOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.next)

@[simp, grind =]
theorem BlockMPtr.readNext_eq_readNext! {ptr : BlockMPtr} {h} :
    ptr.readNext bctx h = ptr.readNext! bctx := by
  simp [BlockMPtr.readNext, BlockMPtr.readNext!]

def BlockMPtr.readParent (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.parent).toInt + Block.Sizes.parent.toInt ≤ bctx.size) : RegionOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.parent) (by grind)

def BlockMPtr.readParent! (ptr : BlockMPtr) : RegionOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.parent)

@[simp, grind =]
theorem BlockMPtr.readParent_eq_readParent! {ptr : BlockMPtr} {h} :
    ptr.readParent bctx h = ptr.readParent! bctx := by
  simp [BlockMPtr.readParent, BlockMPtr.readParent!]

def BlockMPtr.readFirstOp (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.firstOp).toInt + Block.Sizes.firstOp.toInt ≤ bctx.size) : OperationOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.firstOp) (by grind)

def BlockMPtr.readFirstOp! (ptr : BlockMPtr) : OperationOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.firstOp)

@[simp, grind =]
theorem BlockMPtr.readFirstOp_eq_readFirstOp! {ptr : BlockMPtr} {h} :
    ptr.readFirstOp bctx h = ptr.readFirstOp! bctx := by
  simp [BlockMPtr.readFirstOp, BlockMPtr.readFirstOp!]

def BlockMPtr.readLastOp (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.lastOp).toInt + Block.Sizes.lastOp.toInt ≤ bctx.size) : OperationOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.lastOp) (by grind)

def BlockMPtr.readLastOp! (ptr : BlockMPtr) : OperationOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.lastOp)

@[simp, grind =]
theorem BlockMPtr.readLastOp_eq_readLastOp! {ptr : BlockMPtr} {h} :
    ptr.readLastOp bctx h = ptr.readLastOp! bctx := by
  simp [BlockMPtr.readLastOp, BlockMPtr.readLastOp!]

def BlockMPtr.readNumArguments (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.numArguments).toInt + Block.Sizes.numArguments.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Block.Offsets.numArguments) (by grind)

def BlockMPtr.readNumArguments! (ptr : BlockMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Block.Offsets.numArguments)

@[simp, grind =]
theorem BlockMPtr.readNumArguments_eq_readNumArguments! {ptr : BlockMPtr} {h} :
    ptr.readNumArguments bctx h = ptr.readNumArguments! bctx := by
  simp [BlockMPtr.readNumArguments, BlockMPtr.readNumArguments!]

/-! ## Raw accessors for `Region` -/

def RegionMPtr.readFirstBlock (ptr : RegionMPtr)
    (h : (ptr + Region.Offsets.firstBlock).toInt + Region.Sizes.firstBlock.toInt ≤ bctx.size) : BlockOPtr :=
  bctx.mem.read64 (ptr + Region.Offsets.firstBlock) (by grind)

def RegionMPtr.readFirstBlock! (ptr : RegionMPtr) : BlockOPtr :=
  bctx.mem.read64! (ptr + Region.Offsets.firstBlock)

@[simp, grind =]
theorem RegionMPtr.readFirstBlock_eq_readFirstBlock! {ptr : RegionMPtr} {h} :
    ptr.readFirstBlock bctx h = ptr.readFirstBlock! bctx := by
  simp [RegionMPtr.readFirstBlock, RegionMPtr.readFirstBlock!]

def RegionMPtr.readLastBlock (ptr : RegionMPtr)
    (h : (ptr + Region.Offsets.lastBlock).toInt + Region.Sizes.lastBlock.toInt ≤ bctx.size) : BlockOPtr :=
  bctx.mem.read64 (ptr + Region.Offsets.lastBlock) (by grind)

def RegionMPtr.readLastBlock! (ptr : RegionMPtr) : BlockOPtr :=
  bctx.mem.read64! (ptr + Region.Offsets.lastBlock)

@[simp, grind =]
theorem RegionMPtr.readLastBlock_eq_readLastBlock! {ptr : RegionMPtr} {h} :
    ptr.readLastBlock bctx h = ptr.readLastBlock! bctx := by
  simp [RegionMPtr.readLastBlock, RegionMPtr.readLastBlock!]

def RegionMPtr.readParent (ptr : RegionMPtr)
    (h : (ptr + Region.Offsets.parent).toInt + Region.Sizes.parent.toInt ≤ bctx.size) : OperationOPtr :=
  bctx.mem.read64 (ptr + Region.Offsets.parent) (by grind)

def RegionMPtr.readParent! (ptr : RegionMPtr) : OperationOPtr :=
  bctx.mem.read64! (ptr + Region.Offsets.parent)

@[simp, grind =]
theorem RegionMPtr.readParent_eq_readParent! {ptr : RegionMPtr} {h} :
    ptr.readParent bctx h = ptr.readParent! bctx := by
  simp [RegionMPtr.readParent, RegionMPtr.readParent!]
