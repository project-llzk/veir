module

public import Veir.IR.Attribute
public import Veir.IR.OpInfo
public import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/--
  Properties of the `struct.def` operation.

  - `sym_name`: the struct's name. Stored as `StringAttr` (LLZK's
    `SymbolNameAttr` is a `StringAttr` constraint), same convention as
    `global.def` and `function.def`.
  - `const_params`: the template-parameter name list. Only the *older* LLZK
    dialect (the one `llzk-opt --mlir-print-op-generic` in the SP1 corpus
    era emits) carries it — always present there, `const_params = []` for
    non-templated structs. The current dialect has no such attribute, so it
    is `Option` and echoed back exactly as parsed, keeping both spellings
    round-trippable.

  Caveats (same modeling gaps as `global.def`):
  - `Symbol`/`LLZKSymbolTable` traits are not encoded — no uniqueness
    invariant on `sym_name`, and `struct.new`/`struct.readf` references are
    not resolved against the definition.
  - `ParentOneOf<ModuleOp, TemplateOp>` is not encoded — VEIR accepts a
    `struct.def` anywhere.
-/
structure StructDefProperties where
  sym_name : StringAttr
  const_params : Option ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def StructDefProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String StructDefProperties := do
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw "struct.def: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"struct.def: expected 'sym_name' to be a string attribute, got {symAttr}"
  let const_params ← match attrDict["const_params".toUTF8]? with
    | none => pure none
    | some (.arrayAttr arr) => pure (some arr)
    | some attr =>
      throw s!"struct.def: expected 'const_params' to be an array attribute, got {attr}"
  let expected := 1 + (if const_params.isSome then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"struct.def: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { sym_name := sym, const_params }

/--
  Properties of the `struct.field` (older dialect) and `struct.member`
  (current dialect) member-declaration operations. Both spellings carry the
  same payload, so they share this structure; the opcode keeps them apart.

  - `sym_name`: the member's name (`SymbolNameAttr` → `StringAttr`).
  - `type`: the member's declared type. Stored as `Attribute` un-validated,
    same as `global.def`'s `type`.
  - `column` / `signal`: presence of the respective `UnitAttr`s (current
    dialect only; the older dialect never emits them, and absent unit attrs
    are not printed, so round-trip fidelity is preserved for both).

  Note `{llzk.pub}` is a *discardable* attribute (printed after the
  properties dict), so it is handled by the generic attribute machinery,
  not here.
-/
structure StructMemberProperties where
  sym_name : StringAttr
  type : Attribute
  column : Bool
  signal : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def StructMemberProperties.fromAttrDict (opName : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String StructMemberProperties := do
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw s!"{opName}: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"{opName}: expected 'sym_name' to be a string attribute, got {symAttr}"
  let some typeAttr := attrDict["type".toUTF8]?
    | throw s!"{opName}: missing 'type' property"
  let column ← getUnitAttr "column" attrDict
  let signal ← getUnitAttr "signal" attrDict
  let expected := 2 + (if column then 1 else 0) + (if signal then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"{opName}: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { sym_name := sym, type := typeAttr, column, signal }

def StructMemberProperties.toAttrDict (props : StructMemberProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict := Std.HashMap.emptyWithCapacity 4
  dict := dict.insert "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)
  dict := dict.insert "type".toUTF8 props.type
  if props.column then
    dict := dict.insert "column".toUTF8 (Attribute.unitAttr UnitAttr.mk)
  if props.signal then
    dict := dict.insert "signal".toUTF8 (Attribute.unitAttr UnitAttr.mk)
  dict

/--
  Properties of the member-read operations `struct.readf` (older dialect)
  and `struct.readm` (current dialect).

  - `name_ref`: the referenced member. Serialized under the op-appropriate
    key — `field_name` for `readf`, `member_name` for `readm` — which is
    why `fromAttrDict`/`toAttrDict` take the key as an argument.
  - `tableOffset`: optional column offset (`SymbolRefAttr`, `IndexAttr`, or
    `AffineMapAttr`); echoed verbatim when present.
  - `numDimsPerMap` / `mapOpGroupSizes`: the affine-map operand layout
    attributes. `llzk-opt --mlir-print-op-generic` always emits both (empty
    `array<i32>` in the common case); they are `Option` here and echoed
    exactly as parsed so both minimal hand-written tests and real corpus
    output round-trip byte-for-byte. VEIR does not (yet) validate them
    against the operand count.
-/
structure StructReadProperties where
  name_ref : FlatSymbolRefAttr
  tableOffset : Option Attribute
  numDimsPerMap : Option DenseArrayAttr
  mapOpGroupSizes : Option DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def StructReadProperties.fromAttrDict (opName nameKey : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String StructReadProperties := do
  let some refAttr := attrDict[nameKey.toUTF8]?
    | throw s!"{opName}: missing '{nameKey}' property"
  let .flatSymbolRefAttr ref := refAttr
    | throw s!"{opName}: expected '{nameKey}' to be a flat symbol ref, got {refAttr}"
  let tableOffset := attrDict["tableOffset".toUTF8]?
  let numDimsPerMap ← match attrDict["numDimsPerMap".toUTF8]? with
    | none => pure none
    | some (.denseArrayAttr arr) => pure (some arr)
    | some attr =>
      throw s!"{opName}: expected 'numDimsPerMap' to be a dense array attribute, got {attr}"
  let mapOpGroupSizes ← match attrDict["mapOpGroupSizes".toUTF8]? with
    | none => pure none
    | some (.denseArrayAttr arr) => pure (some arr)
    | some attr =>
      throw s!"{opName}: expected 'mapOpGroupSizes' to be a dense array attribute, got {attr}"
  let expected := 1 + (if tableOffset.isSome then 1 else 0)
    + (if numDimsPerMap.isSome then 1 else 0) + (if mapOpGroupSizes.isSome then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"{opName}: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { name_ref := ref, tableOffset, numDimsPerMap, mapOpGroupSizes }

def StructReadProperties.toAttrDict (nameKey : String) (props : StructReadProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict := Std.HashMap.emptyWithCapacity 4
  dict := dict.insert nameKey.toUTF8 (Attribute.flatSymbolRefAttr props.name_ref)
  if let some off := props.tableOffset then
    dict := dict.insert "tableOffset".toUTF8 off
  if let some arr := props.numDimsPerMap then
    dict := dict.insert "numDimsPerMap".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.mapOpGroupSizes then
    dict := dict.insert "mapOpGroupSizes".toUTF8 (Attribute.denseArrayAttr arr)
  dict

/--
  Properties of the member-write operations `struct.writef` (older dialect)
  and `struct.writem` (current dialect): just the member reference, keyed
  `field_name` / `member_name` respectively.
-/
structure StructWriteProperties where
  name_ref : FlatSymbolRefAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def StructWriteProperties.fromAttrDict (opName nameKey : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String StructWriteProperties := do
  if attrDict.size > 1 then
    throw s!"{opName}: expected only '{nameKey}' property, got {attrDict.size} properties"
  let some refAttr := attrDict[nameKey.toUTF8]?
    | throw s!"{opName}: missing '{nameKey}' property"
  let .flatSymbolRefAttr ref := refAttr
    | throw s!"{opName}: expected '{nameKey}' to be a flat symbol ref, got {refAttr}"
  return { name_ref := ref }

end

end Veir
