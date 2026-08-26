module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Felt.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Felt where
| const
| add
| sub
| mul
| pow
| div
| uintdiv
| sintdiv
| umod
| smod
| neg
| inv
| bit_and
| bit_or
| bit_xor
| bit_not
| shl
| shr
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Felt.propertiesOf (op : Felt) : Type :=
match op with
| .const => FeltConstProperties
| _ => Unit

def Felt.fromAttrDict
    (op : Felt) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Felt.propertiesOf op) := by
  cases op
  case const => exact FeltConstProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Felt.toAttrDict
    (op : Felt) (props : Felt.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .const =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "value".toUTF8 (Attribute.feltConstAttr props.value)
  | _ => Std.HashMap.emptyWithCapacity 0

/-- Every `felt` operation is pure field arithmetic. -/
def Felt.getEffects
    (_op : Felt) (_props : Felt.propertiesOf _op) : MemoryEffects :=
  .none

def Felt.isConstantLike (op : Felt) : Bool :=
  match op with
  | .const => true
  | _ => false

def Felt.hasSSADominance (_op : Felt) (_index : Nat) : Bool :=
  true

#generate_dialect Felt

instance : IsOpCode Felt where
  fromName := Felt.fromName
  name := Felt.name
  propertiesOf := Felt.propertiesOf
  fromAttrDict := Felt.fromAttrDict
  toAttrDict := Felt.toAttrDict

/--
Verify the local invariants of a `felt` operation in any operation-info type
containing the `felt` dialect.
-/
@[expose]
def Felt.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Felt] (opType : Felt) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .const => op.verifyPlainOpCounts ctx opIn 0 1
  | .add | .sub | .mul | .pow | .div
  | .uintdiv | .sintdiv | .umod | .smod
  | .bit_and | .bit_or | .bit_xor
  | .shl | .shr => op.verifyPlainOpCounts ctx opIn 2 1
  | .neg | .inv | .bit_not => op.verifyPlainOpCounts ctx opIn 1 1

instance : HasOpInfo Felt where
  verifyLocalInvariants := Felt.verifyLocalInvariants
  getEffects := Felt.getEffects
  isConstantLike := Felt.isConstantLike
  hasSSADominance := Felt.hasSSADominance

end

end Veir
