module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Struct.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
  LLZK's struct dialect. Both mnemonic generations are registered as
  distinct opcodes so both real corpora parse and round-trip unchanged:
  the older dialect (what the SP1-era `llzk-opt --mlir-print-op-generic`
  emits) spells member ops `field`/`readf`/`writef` with a `field_name`
  key; the current dialect spells them `member`/`readm`/`writem` with a
  `member_name` key.
-/
@[opcodes]
inductive Struct where
| «def»
| field
| member
| new
| readf
| readm
| writef
| writem
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Struct.propertiesOf (op : Struct) : Type :=
match op with
| .«def» => StructDefProperties
| .field | .member => StructMemberProperties
| .new => Unit
| .readf | .readm => StructReadProperties
| .writef | .writem => StructWriteProperties

def Struct.fromAttrDict
    (op : Struct) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Struct.propertiesOf op) := by
  cases op
  case «def» => exact StructDefProperties.fromAttrDict attrDict
  case field => exact StructMemberProperties.fromAttrDict "struct.field" attrDict
  case member => exact StructMemberProperties.fromAttrDict "struct.member" attrDict
  case new => exact .ok ()
  case readf => exact StructReadProperties.fromAttrDict "struct.readf" "field_name" attrDict
  case readm => exact StructReadProperties.fromAttrDict "struct.readm" "member_name" attrDict
  case writef => exact StructWriteProperties.fromAttrDict "struct.writef" "field_name" attrDict
  case writem => exact StructWriteProperties.fromAttrDict "struct.writem" "member_name" attrDict

def Struct.toAttrDict
    (op : Struct) (props : Struct.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op, props with
  | .«def», props => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    dict := dict.insert "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)
    if let some cp := props.const_params then
      dict := dict.insert "const_params".toUTF8 (Attribute.arrayAttr cp)
    dict
  | .field, props | .member, props => props.toAttrDict
  | .new, _ => Std.HashMap.emptyWithCapacity 0
  | .readf, props => props.toAttrDict "field_name"
  | .readm, props => props.toAttrDict "member_name"
  | .writef, props =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "field_name".toUTF8 (Attribute.flatSymbolRefAttr props.name_ref)
  | .writem, props =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "member_name".toUTF8 (Attribute.flatSymbolRefAttr props.name_ref)

/--
`struct.def` and the member declarations are symbol-carrying declarations
with no results; VEIR does not model the `Symbol` trait, so they report
`.unknown` to keep DCE from erasing them (the `global.def` precedent).
Reads/writes carry the obvious effects; `struct.new` allocates.
-/
def Struct.getEffects
    (op : Struct) (_props : Struct.propertiesOf op) : MemoryEffects :=
  match op with
  | .«def» | .field | .member => .unknown
  | .new => .allocate
  | .readf | .readm => .read
  | .writef | .writem => .write

def Struct.isConstantLike (_op : Struct) : Bool :=
  false

def Struct.isIsolatedFromAbove (op : Struct) : Bool :=
  match op with
  | .«def» => true
  | _ => false

/-- The `struct.def` body is a graph region (LLZK's `GraphRegionNoTerminator`):
    member declarations and the `compute`/`constrain` functions in any order. -/
def Struct.getRegionKind (op : Struct) (_index : Nat) : RegionKind :=
  match op with
  | .«def» => .Graph
  | _ => .SSACFG

def Struct.hasSSADominance (op : Struct) (_index : Nat) : Bool :=
  match op with
  | .«def» => false
  | _ => true

def Struct.hasNoTerminator (op : Struct) (_index : Nat) : Bool :=
  match op with
  | .«def» => true
  | _ => false

#generate_dialect Struct

instance : IsOpCode Struct where
  fromName := Struct.fromName
  name := Struct.name
  propertiesOf := Struct.propertiesOf
  fromAttrDict := Struct.fromAttrDict
  toAttrDict := Struct.toAttrDict

/--
Verify the local invariants of a `struct` operation in any operation-info
type containing the `struct` dialect.
-/
@[expose]
def Struct.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Struct] (opType : Struct) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .«def» => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "struct.def: Expected 0 operand(s)"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "struct.def: Expected 0 result(s)"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "struct.def: Expected 1 region (the struct body)"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "struct.def: Expected 0 successors"
  | .field | .member => op.verifyPlainOpCounts ctx opIn 0 0
  | .new => op.verifyPlainOpCounts ctx opIn 0 1
  -- Reads take the component plus a variadic tail of affine-map operands,
  -- so only a lower bound on the operand count is checked.
  | .readf | .readm => do
    let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
    if op.getNumOperands ctx.raw opIn < 1 then
      throw s!"{instrName}: Expected at least 1 operand (the component)"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw s!"{instrName}: Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw s!"{instrName}: Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw s!"{instrName}: Expected 0 successors"
  | .writef | .writem => op.verifyPlainOpCounts ctx opIn 2 0

instance : HasOpInfo Struct where
  verifyLocalInvariants := Struct.verifyLocalInvariants
  getEffects := Struct.getEffects
  isConstantLike := Struct.isConstantLike
  getRegionKind := Struct.getRegionKind
  hasSSADominance := Struct.hasSSADominance
  hasNoTerminator := Struct.hasNoTerminator
  isIsolatedFromAbove := Struct.isIsolatedFromAbove

end

end Veir
