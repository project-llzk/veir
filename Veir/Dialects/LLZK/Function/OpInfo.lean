module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Function.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Function_ where
| «def»
| return
-- `call` deferred to Phase C (variadic-of-variadic + SymbolRefAttr).
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Function_.propertiesOf (op : Function_) : Type :=
match op with
| .«def» => FunctionDefProperties
| .return => Unit

def Function_.fromAttrDict
    (op : Function_) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Function_.propertiesOf op) := by
  cases op
  case «def» => exact FunctionDefProperties.fromAttrDict attrDict
  case «return» => exact .ok ()

def Function_.toAttrDict
    (op : Function_) (props : Function_.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .«def» => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    dict := dict.insert "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)
    dict := dict.insert "function_type".toUTF8 (Attribute.functionType props.function_type)
    dict
  | .return => Std.HashMap.emptyWithCapacity 0

def Function_.getEffects
    (_op : Function_) (_props : Function_.propertiesOf _op) : MemoryEffects :=
  .none

def Function_.isConstantLike (_op : Function_) : Bool :=
  false

def Function_.hasSSADominance (_op : Function_) (_index : Nat) : Bool :=
  true

def Function_.isTerminator (op : Function_) : Bool :=
  match op with
  | .return => true
  | .«def» => false

#generate_dialect Function_

instance : IsOpCode Function_ where
  fromName := Function_.fromName
  name := Function_.name
  propertiesOf := Function_.propertiesOf
  fromAttrDict := Function_.fromAttrDict
  toAttrDict := Function_.toAttrDict

def Function_.functionInterface? (op : Function_) :
    Option (FunctionOpInterface (Function_.propertiesOf op)) :=
  match op with
  | .«def» =>
    some
      { getSymName := fun props => props.sym_name
        getFunctionType := fun props => props.function_type
        setFunctionType := fun props functionType =>
          { props with function_type := functionType } }
  | .return => none

/--
Verify the local invariants of a `function` operation in any operation-info
type containing the `function` dialect.
-/
@[expose]
def Function_.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Function_] (opType : Function_) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .«def» => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "function.def: Expected 0 operand(s)"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "function.def: Expected 0 result(s)"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "function.def: Expected 1 region (the function body)"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "function.def: Expected 0 successors"
  -- Variadic operands: no operand-count check.
  | .return => op.verifyTerminatorCounts ctx opIn 0

instance : HasOpInfo Function_ where
  verifyLocalInvariants := Function_.verifyLocalInvariants
  getEffects := Function_.getEffects
  isConstantLike := Function_.isConstantLike
  functionInterface? := Function_.functionInterface?
  hasSSADominance := Function_.hasSSADominance
  isTerminator := Function_.isTerminator

end

end Veir
