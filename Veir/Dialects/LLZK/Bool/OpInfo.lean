module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Bool.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Bool_ where
| and
| or
| xor
| not
| assert
| cmp
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Bool_.propertiesOf (op : Bool_) : Type :=
match op with
| .assert => BoolAssertProperties
| .cmp => BoolCmpProperties
| _ => Unit

def Bool_.fromAttrDict
    (op : Bool_) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Bool_.propertiesOf op) := by
  cases op
  case assert => exact BoolAssertProperties.fromAttrDict attrDict
  case cmp => exact BoolCmpProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Bool_.toAttrDict
    (op : Bool_) (props : Bool_.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .assert =>
    match props.msg with
    | some m => (Std.HashMap.emptyWithCapacity 1).insert "msg".toUTF8 (Attribute.stringAttr m)
    | none => Std.HashMap.emptyWithCapacity 0
  | .cmp =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr props.predicate)
  | _ => Std.HashMap.emptyWithCapacity 0

/--
The boolean connectives and comparisons are pure. `bool.assert` emits an
assertion into the circuit and has no results, so it must report an effect
or DCE would erase it.
-/
def Bool_.getEffects
    (op : Bool_) (_props : Bool_.propertiesOf op) : MemoryEffects :=
  match op with
  | .assert => .write
  | .and | .or | .xor | .not | .cmp => .none

def Bool_.isConstantLike (_op : Bool_) : Bool :=
  false

def Bool_.hasSSADominance (_op : Bool_) (_index : Nat) : Bool :=
  true

#generate_dialect Bool_

instance : IsOpCode Bool_ where
  fromName := Bool_.fromName
  name := Bool_.name
  propertiesOf := Bool_.propertiesOf
  fromAttrDict := Bool_.fromAttrDict
  toAttrDict := Bool_.toAttrDict

/--
Verify the local invariants of a `bool` operation in any operation-info type
containing the `bool` dialect.
-/
@[expose]
def Bool_.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Bool_] (opType : Bool_) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .and | .or | .xor => op.verifyPlainOpCounts ctx opIn 2 1
  | .not => op.verifyPlainOpCounts ctx opIn 1 1
  | .assert => op.verifyPlainOpCounts ctx opIn 1 0
  | .cmp => op.verifyPlainOpCounts ctx opIn 2 1

instance : HasOpInfo Bool_ where
  verifyLocalInvariants := Bool_.verifyLocalInvariants
  getEffects := Bool_.getEffects
  isConstantLike := Bool_.isConstantLike
  hasSSADominance := Bool_.hasSSADominance

end

end Veir
