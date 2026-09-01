module

public import Veir.IR.Attribute
public import Veir.IR.OpInfo

namespace Veir

public section

/--
  Properties of the `function.def` operation (Phase F.5).

  Carries the two required attributes:

  - `sym_name : StringAttr` per LLZK's `SymbolNameAttr` constraint
    (Gotcha 5 in `harness/porting-notes.md`). Generic form prints
    `<{sym_name = "name", ...}>`.
  - `function_type : FunctionType` — the signature. LLZK's TableGen
    declares this as `TypeAttrOf<FunctionType>` and the C++ verifier
    rejects a `function.def` without it, so the differential
    round-trip requires us to emit it. Stored as the underlying
    `FunctionType` (VEIR's type/attribute hierarchy lets us treat the
    wrapping `Attribute.functionType` case as a type attribute).

  Deferred for this prototype:
  - `arg_attrs`/`res_attrs` (ArrayAttrs of DictAttrs) — optional in
    LLZK, used by argument-attribute decorators (`{llzk.pub}`, …).
    Round-trip works without them when no decorators are present.
-/
structure FunctionDefProperties where
  sym_name : StringAttr
  function_type : FunctionType
deriving Inhabited, Repr, Hashable, DecidableEq

def FunctionDefProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FunctionDefProperties := do
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw "function.def: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"function.def: expected 'sym_name' to be a string attribute, got {symAttr}"
  let some ftAttr := attrDict["function_type".toUTF8]?
    | throw "function.def: missing 'function_type' property"
  let .functionType ft := ftAttr
    | throw s!"function.def: expected 'function_type' to be a function type, got {ftAttr}"
  return { sym_name := sym, function_type := ft }

/--
  Properties of the `function.call` operation.

  - `callee`: the target, as a possibly nested reference — the full path
    from the root module, e.g. `@do_stuff` or `@OtherStruct::@compute`.
    Stored as `SymbolRefAttr`; a flat `@name` is normalized to empty
    `nestedRefs` (the printed generic form is identical either way).
  - `operandSegmentSizes`: `function.call` has two variadic operand groups
    (`argOperands` and the affine-map `mapOperands`), so MLIR's
    `AttrSizedOperandSegments` adds this layout attribute.
  - `numDimsPerMap` / `mapOpGroupSizes`: the affine-map operand layout
    pair, as on `struct.readf`/`array.new`.
  - `templateParams`: optional instantiation list for callees inside a
    `poly.template` region.

  The four optional attributes are echoed back exactly as parsed; VEIR does
  not (yet) validate the segment sizes against the operand count, nor
  resolve `callee` against a `function.def`.
-/
structure FunctionCallProperties where
  callee : SymbolRefAttr
  operandSegmentSizes : Option DenseArrayAttr
  numDimsPerMap : Option DenseArrayAttr
  mapOpGroupSizes : Option DenseArrayAttr
  templateParams : Option ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def FunctionCallProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FunctionCallProperties := do
  let callee ← match attrDict["callee".toUTF8]? with
    | some (.symbolRefAttr ref) => pure ref
    | some (.flatSymbolRefAttr flat) => pure { rootRef := flat.value, nestedRefs := #[] }
    | some attr =>
      throw s!"function.call: expected 'callee' to be a symbol reference, got {attr}"
    | none => throw "function.call: missing 'callee' property"
  let getDense (key : String) : Except String (Option DenseArrayAttr) := do
    match attrDict[key.toUTF8]? with
    | none => return none
    | some (.denseArrayAttr arr) => return (some arr)
    | some attr =>
      throw s!"function.call: expected '{key}' to be a dense array attribute, got {attr}"
  let operandSegmentSizes ← getDense "operandSegmentSizes"
  let numDimsPerMap ← getDense "numDimsPerMap"
  let mapOpGroupSizes ← getDense "mapOpGroupSizes"
  let templateParams ← match attrDict["templateParams".toUTF8]? with
    | none => pure none
    | some (.arrayAttr arr) => pure (some arr)
    | some attr =>
      throw s!"function.call: expected 'templateParams' to be an array attribute, got {attr}"
  let expected := 1 + (if operandSegmentSizes.isSome then 1 else 0)
    + (if numDimsPerMap.isSome then 1 else 0) + (if mapOpGroupSizes.isSome then 1 else 0)
    + (if templateParams.isSome then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"function.call: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { callee, operandSegmentSizes, numDimsPerMap, mapOpGroupSizes, templateParams }

def FunctionCallProperties.toAttrDict (props : FunctionCallProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict := Std.HashMap.emptyWithCapacity 5
  dict := dict.insert "callee".toUTF8 (Attribute.symbolRefAttr props.callee)
  if let some arr := props.operandSegmentSizes then
    dict := dict.insert "operandSegmentSizes".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.numDimsPerMap then
    dict := dict.insert "numDimsPerMap".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.mapOpGroupSizes then
    dict := dict.insert "mapOpGroupSizes".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.templateParams then
    dict := dict.insert "templateParams".toUTF8 (Attribute.arrayAttr arr)
  dict

end

end Veir
