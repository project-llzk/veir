module

public import Veir.IR.Attribute
public import Veir.IR.OpInfo

namespace Veir

public section

/--
  Properties of the `array.new` operation.

  `array.new` has two variadic operand groups (the initializing elements and
  the affine-map instantiation operands), so MLIR's
  `AttrSizedOperandSegments` gives it an `operandSegmentSizes` attribute in
  addition to the `numDimsPerMap`/`mapOpGroupSizes` layout pair shared with
  `struct.readf`/`readm` and `function.call`.

  All three are `Option DenseArrayAttr` and echoed back exactly as parsed:
  `llzk-opt --mlir-print-op-generic` always emits them, minimal hand-written
  tests may omit them, and both must round-trip byte-for-byte. VEIR does not
  (yet) validate them against the operand count.
-/
structure ArrayNewProperties where
  operandSegmentSizes : Option DenseArrayAttr
  numDimsPerMap : Option DenseArrayAttr
  mapOpGroupSizes : Option DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

private def getOptionalDenseArrayAttr (opName key : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Option DenseArrayAttr) := do
  match attrDict[key.toUTF8]? with
  | none => return none
  | some (.denseArrayAttr arr) => return (some arr)
  | some attr =>
    throw s!"{opName}: expected '{key}' to be a dense array attribute, got {attr}"

def ArrayNewProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ArrayNewProperties := do
  let operandSegmentSizes ← getOptionalDenseArrayAttr "array.new" "operandSegmentSizes" attrDict
  let numDimsPerMap ← getOptionalDenseArrayAttr "array.new" "numDimsPerMap" attrDict
  let mapOpGroupSizes ← getOptionalDenseArrayAttr "array.new" "mapOpGroupSizes" attrDict
  let expected := (if operandSegmentSizes.isSome then 1 else 0)
    + (if numDimsPerMap.isSome then 1 else 0) + (if mapOpGroupSizes.isSome then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"array.new: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { operandSegmentSizes, numDimsPerMap, mapOpGroupSizes }

def ArrayNewProperties.toAttrDict (props : ArrayNewProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict := Std.HashMap.emptyWithCapacity 3
  if let some arr := props.operandSegmentSizes then
    dict := dict.insert "operandSegmentSizes".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.numDimsPerMap then
    dict := dict.insert "numDimsPerMap".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.mapOpGroupSizes then
    dict := dict.insert "mapOpGroupSizes".toUTF8 (Attribute.denseArrayAttr arr)
  dict

end

end Veir
