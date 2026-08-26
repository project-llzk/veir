module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Constrain where
| eq
-- `in` deferred until Array types land (Phase D.3).
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Constrain.propertiesOf (_op : Constrain) : Type :=
  Unit

def Constrain.fromAttrDict
    (_op : Constrain) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Constrain.propertiesOf _op) :=
  .ok ()

def Constrain.toAttrDict
    (_op : Constrain) (_props : Constrain.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

/--
`constrain.eq` emits a constraint into the circuit. It has no results, so it
must report an effect or DCE would erase the constraint system.
-/
def Constrain.getEffects
    (_op : Constrain) (_props : Constrain.propertiesOf _op) : MemoryEffects :=
  .write

def Constrain.isConstantLike (_op : Constrain) : Bool :=
  false

def Constrain.hasSSADominance (_op : Constrain) (_index : Nat) : Bool :=
  true

#generate_dialect Constrain

instance : IsOpCode Constrain where
  fromName := Constrain.fromName
  name := Constrain.name
  propertiesOf := Constrain.propertiesOf
  fromAttrDict := Constrain.fromAttrDict
  toAttrDict := Constrain.toAttrDict

/--
Verify the local invariants of a `constrain` operation in any operation-info
type containing the `constrain` dialect.
-/
@[expose]
def Constrain.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Constrain] (opType : Constrain) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .eq => op.verifyPlainOpCounts ctx opIn 2 0

instance : HasOpInfo Constrain where
  verifyLocalInvariants := Constrain.verifyLocalInvariants
  getEffects := Constrain.getEffects
  isConstantLike := Constrain.isConstantLike
  hasSSADominance := Constrain.hasSSADominance

end

end Veir
