import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas

namespace Veir
namespace Example

variable {OpInfo : Type} [HasOpInfo OpInfo]

theorem matchOp_implies :
  matchOp op ctx opType numOperands = some (operands, properties) →
  op.getOpType! ctx = opType ∧
  op.getNumOperands! ctx = numOperands ∧
  op.getNumResults! ctx = 1 ∧
  operands = op.getOperands! ctx ∧
  properties = op.getProperties! ctx opType := by
  simp only [matchOp]
  simp only [guard, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, ite_eq_left_iff,
    reduceCtorEq, imp_false, Decidable.not_not, Option.some.injEq, Prod.mk.injEq, exists_const,
    and_imp]
  intros
  grind

theorem matchOp_interpretOp
  (opInBounds : op.InBounds ctx) :
  matchOp op ctx opType numOperands = some (operands, properties) →
  interpretOp ctx op state = some (.ok (newState, cf)) →
  ∃ values newValue,
    operands.mapM state.variables.getVar? = some values ∧
    interpretOp' opType properties (op.getResultTypes! ctx) values (op.getSuccessors! ctx) state.memory =
      some (.ok (#[newValue], newMem, cf)) ∧
    newState = ⟨state.variables.setVar (op.getResult 0) newValue, mem'⟩ := by
  intro hmatch hinterp
  have ⟨hOpType, hNumOperands, hNumResults, hOperands, hProperties⟩ := matchOp_implies hmatch
  subst opType properties
  simp only [interpretOp] at hinterp
  split at hinterp; rotate_left; grind; rename_i _ values hValues
  exists values
  simp only [bind] at hinterp
  split at hinterp; grind; grind; rename_i _ res hinterp'
  have ⟨resValues, resMem, cf⟩ := res
  have : resValues.size = 1 := by sorry -- Missing lemma about number of results and interpretation
  exists resValues[0]
  have : resValues = #[resValues[0]] := by grind
  constructor
  · grind [VariableState.getOperandValues]
  · simp only [Interp, hinterp', Option.some.injEq, UBOr.ok.injEq, Prod.mk.injEq]
    simp only [Interp, pure, Option.some.injEq, UBOr.ok.injEq, Prod.mk.injEq] at hinterp
    have ⟨_, _⟩ := hinterp; subst cf newState
    simp only [and_true, InterpreterState.mk.injEq]
    sorry
    --grind [InterpreterState.setResultValues, InterpreterState.setResultValues_loop]


theorem matchOp_interpretOp'
  (opInBounds : op.InBounds ctx) :
  matchOp op ctx opType numOperands = some (operands, properties) →
  interpretOp ctx op state = some (.ok (newState, cf)) →
  ∃ values newValue,
    operands.mapM state.variables.getVar? = some values ∧
    newState.variables.getVar? (op.getResult 0) = some newValue ∧
    interpretOp' opType properties (op.getResultTypes! ctx) values (op.getSuccessors! ctx) state.memory =
    some (#[newValue], newState.memory, cf) := by
  sorry
  -- grind [matchOp_interpretOp]

def matchAddi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.arith .addi)) := do
  let (op, properties) ← matchOp op ctx (.arith .addi) 2
  return (op[0]!, op[1]!, properties)

theorem matchAddi_implies :
  matchAddi op ctx = some (lhs, rhs, properties) →
  op.getOpType! ctx = .arith .addi ∧
  op.getNumResults! ctx = 1 ∧
  op.getOperands! ctx = #[lhs, rhs] ∧
  op.getOperand! ctx 0 = lhs ∧
  op.getOperand! ctx 1 = rhs ∧
  properties = op.getProperties! ctx (.arith .addi) := by
  intro hmatch
  simp only [matchAddi, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq, Prod.exists] at hmatch
  grind [matchOp_implies]

theorem matchAddi_interpretOp
  (opInBounds : op.InBounds ctx) :
  matchAddi op ctx = some (lhs, rhs, properties) →
  interpretOp ctx op state = some (newState, cf) →
  ∃ lhsVal rhsVal newValue mem',
    state.variables.getVar? lhs = some lhsVal ∧
    state.variables.getVar? rhs = some rhsVal ∧
    interpretOp' (.arith .addi) properties (op.getResultTypes! ctx) #[lhsVal, rhsVal] #[] state.memory = some (#[newValue], mem', cf) ∧
    newState = ⟨state.variables.setVar (op.getResult 0) newValue, newState.memory⟩ := by
  /-intro hmatch
  simp only [matchAddi, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq, Prod.exists] at hmatch
  have ⟨operands, properties, hmatchOp, hlhs, hrhs, hprop⟩ := hmatch
  have ⟨hOpType, hNumOperands, hNumResults, hOperands, hProperties⟩ := matchOp_implies hmatchOp
  intro hinterp
  have ⟨values, newValue, hValues, hinterp', hnewState⟩ := matchOp_interpretOp opInBounds hmatchOp hinterp
  have : operands = #[lhs, rhs] := by grind
  subst this
  simp only [List.mapM_toArray, List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Option.map_eq_map, Option.map_bind, Option.bind_eq_some_iff,
    Function.comp_apply, Option.some.injEq, Option.map_some] at hValues
  have : (op.getResultTypes! ctx) = #[((op.getResult 0).get! ctx).type] := by grind
  have : (op.getSuccessors! ctx) = #[] := by sorry
  grind-/
  sorry

theorem matchAddi_interpretOp'
  (opInBounds : op.InBounds ctx) :
  matchAddi op ctx = some (lhs, rhs, properties) →
  interpretOp ctx op state = some (newState, cf) →
  ∃ lhsVal rhsVal newValue,
    state.variables.getVar? lhs = some lhsVal ∧
    state.variables.getVar? rhs = some rhsVal ∧
    newState.variables.getVar? (op.getResult 0) = some newValue ∧
    interpretOp' (.arith .addi) properties #[((op.getResult 0).get! ctx).type] #[lhsVal, rhsVal] #[] state.memory = some (#[newValue], newState.memory, cf) := by
  sorry

theorem interpretOp'_arith_addi_eq_some_implies :
    interpretOp' (OpCode.arith Arith.addi) properties #[resType] #[lhsVal, rhsVal] #[] memory = some (#[res], memory', cf) →
    ∃ bw intLhs intRhs,
    lhsVal = .int bw intLhs ∧
    rhsVal = .int bw intRhs ∧
    res = .int bw (intLhs.add intRhs properties.nsw properties.nuw) ∧
    cf = none ∧
    memory = memory' := by
  intro h
  --simp only [interpretOp', ne_eq, Option.pure_def, dite_not] at h
  --split at h; rotate_left; grind; rename_i _ bwLhs intLhsVal bwRhs intRhsVal hTemp
  --simp only [List.cons.injEq, and_true] at hTemp; have ⟨_,_⟩ := hTemp; clear hTemp; subst lhsVal rhsVal
  --split at h; rotate_left; grind; subst bwRhs
  --simp at h; have ⟨_, _⟩ := h; clear h; subst cf res
  sorry
  -- simp only [Data.LLVM.Int.cast, BitVec.cast_eq]
  -- exists bwLhs, intLhsVal, intRhsVal
  -- grind

theorem matchAddi_interpretOp_unfold (opInBounds : op.InBounds ctx) :
    matchAddi op ctx = some (lhs, rhs, properties) →
    interpretOp ctx op state = some (newState, cf) →
    ∀ bw isType, lhs.getType! ctx = ⟨Attribute.integerType (IntegerType.mk bw), isType⟩ →
    ∃ intLhs intRhs,
    state.variables.getVar? lhs = some (RuntimeValue.int bw intLhs) ∧
    state.variables.getVar? rhs = some (RuntimeValue.int bw intRhs) ∧
    newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int bw (intLhs.add intRhs properties.nsw properties.nuw)) ∧
    cf = none := by
  sorry
  --grind [matchAddi_interpretOp', interpretOp'_arith_addi_eq_some_implies]

def matchConstantOp (op : OperationPtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .arith .constant := op.getOpType! ctx | none
  let properties := op.getProperties! ctx (.arith .constant)
  return properties.value

theorem matchConstantOp_implies :
    matchConstantOp op ctx = some properties →
    op.getOpType! ctx = .arith .constant ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[] ∧
    properties = (op.getProperties! ctx (.arith .constant)).value := by
  sorry

theorem matchConstantOp_interpretOp'
    (opInBounds : op.InBounds ctx) :
    matchConstantOp op ctx = some (properties) →
    interpretOp ctx op state = some (newState, cf) →
    ∃ newValue,
      newState.variables.getVar? (op.getResult 0) = some newValue ∧
      interpretOp' (.arith .constant) (ArithConstantProperties.mk properties) #[((op.getResult 0).get! ctx).type] #[] #[] state.memory = some (#[newValue], newState.memory, cf) := by
  sorry

theorem interpretOp'_arith_constant_eq_some_implies :
    interpretOp' (OpCode.arith Arith.constant) properties #[resType] #[] #[] memory = some (#[res], newMemory, cf) →
    ∃ intType,
    resType = Attribute.integerType intType ∧
    res = RuntimeValue.int intType.bitwidth (Data.LLVM.Int.val (BitVec.ofInt intType.bitwidth properties.value.value)) ∧
    cf = none ∧
    memory = newMemory := by
  unfold interpretOp'
  simp only [bind, liftM, monadLift, MonadLift.monadLift]
  sorry
  -- grind

theorem matchConstantOp_interpretOp_unfold (opInBounds : op.InBounds ctx) :
    matchConstantOp op ctx = some properties →
    interpretOp ctx op state = some (newState, cf) →
    newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int properties.type.bitwidth (Data.LLVM.Int.val (BitVec.ofInt properties.type.bitwidth properties.value))) ∧
    cf = none := by
  sorry
  --grind [matchConstantOp_interpretOp', interpretOp'_arith_constant_eq_some_implies]

theorem matchConstantOp_interpretOp_unfold' (opInBounds : op.InBounds ctx) :
    matchConstantOp op ctx = some properties →
    interpretOp ctx op state = some (newState, cf) →
    ∀ bw, bw = properties.type.bitwidth →
    newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int bw (Data.LLVM.Int.val (BitVec.ofInt bw properties.value))) ∧
    cf = none := by
  grind [matchConstantOp_interpretOp_unfold]

def addIConstantFolding (ctx: WfIRContext OpCode) (op: OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  -- Match an `arith.addi`
  let (lhs, rhs, addProp) ← matchAddi op ctx
  if addProp.nsw || addProp.nuw then
    return (ctx, none)
  let lhsOp ← lhs.getDefiningOp! ctx.raw
  let rhsOp ← rhs.getDefiningOp! ctx.raw
  let lhsConst ← matchConstantOp lhsOp ctx
  let rhsConst ← matchConstantOp rhsOp ctx

  -- Sum both constant values
  let ⟨.integerType intType, _⟩ := lhs.getType! ctx.raw | none
  let newConst := ArithConstantProperties.mk (IntegerAttr.mk ((BitVec.ofInt intType.bitwidth lhsConst.value) + (BitVec.ofInt intType.bitwidth rhsConst.value)).toInt intType)
  let (ctx, newOp) ← WfRewriter.createOp ctx (.arith .constant) #[intType] #[] #[] #[] newConst none sorry sorry sorry sorry
  return (ctx, some (#[newOp], #[newOp.getResult 0]))

theorem ValuePtr.getDefiningOp!.numResults_zero {ctx : IRContext OpInfo} {op : OperationPtr} {value : ValuePtr} :
    value.getDefiningOp! ctx = op →
    op.getNumResults! ctx = 1 →
    value = op.getResult 0 := by
  sorry

grind_pattern ValuePtr.getDefiningOp!.numResults_zero =>
    value.getDefiningOp! ctx, op.getNumResults! ctx

theorem addIConstantFolding_preservesSemantics :
    LocalRewritePattern.PreservesSemantics addIConstantFolding h := by
  -- Unfold definition and cleanup hypotheses
  simp only [LocalRewritePattern.PreservesSemantics, addIConstantFolding]
  intros ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq, Prod.exists] at hpattern
  have ⟨lhs, rhs, properties, matchAdd, hpattern₂⟩ := hpattern
  split at hpattern₂; grind; rename_i hProperties; clear hpattern
  simp [Option.bind_eq_some_iff] at hpattern₂
  have ⟨lhsOp, hLhsOp, rhsOp, hRhsOp, lhsConst, matchLhs, rhsConst, matchRhs, hpattern₃⟩ := hpattern₂; clear hpattern₂
  split at hpattern₃; rotate_left; grind; rename_i intType intTypeIsType hIntType
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq, Prod.exists] at hpattern₃
  have ⟨newCtx', newOp, hNewCtx, _, _, _⟩ := hpattern₃; clear hpattern₃
  subst newCtx' newOps newValues
  simp only [liftM, monadLift, MonadLift.monadLift, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, List.getElem_toArray, List.getElem_singleton,
    forall_eq]

  -- Introduce match information
  have := matchConstantOp_implies matchLhs
  have := matchConstantOp_implies matchRhs
  have := matchAddi_implies matchAdd

  -- Introduce verification information
  have : lhsOp.Verified ctx := by sorry
  have := OperationPtr.Verified.arith_constant this
  have : rhsOp.Verified ctx := by sorry
  have := OperationPtr.Verified.arith_constant this
  have : op.Verified ctx := by sorry
  have ⟨_, _, _, _, intType', _⟩ := OperationPtr.Verified.arith_addi this (by grind)

  have : lhs = ValuePtr.opResult (lhsOp.getResult 0) := by grind
  have : rhs = ValuePtr.opResult (rhsOp.getResult 0) := by grind
  subst lhs rhs

  -- Introduce bw that we will use for each variable
  let bw := intType.bitwidth

  -- Unfold interpretation of the original add operation
  have ⟨intLhs, intRhs, hIntLhs, hIntRhs, hAddRes, hCf⟩ := matchAddi_interpretOp_unfold (by grind) matchAdd hinterp bw (by grind) (by grind [cases IntegerType])
  subst cf; clear hinterp

  -- Introduce equation lemma for `lhs`, and unfold the interpretation of it
  have ⟨cfLhs, hInterpLhs⟩ := stateWf lhsOp (by grind) (by sorry) (by grind)
  have ⟨hLhsRes, hCf⟩ := matchConstantOp_interpretOp_unfold' (by grind) matchLhs hInterpLhs bw (by grind)
  subst cfLhs

  -- Introduce equation lemma for `rhs`, and unfold the interpretation of it
  have ⟨cfRhs, hInterpRhs⟩ := stateWf rhsOp (by grind) (by sorry) (by grind)
  have ⟨hRhsRes, hCf⟩ := matchConstantOp_interpretOp_unfold' (by grind) matchRhs hInterpRhs bw (by sorry)
  subst cfRhs

  -- We can remove bw now
  subst bw

  -- Match operands information with their interpretation results
  simp [hIntLhs] at hLhsRes
  simp [hIntRhs] at hRhsRes
  subst intLhs intRhs

  -- Resolve the new state values
  simp only [hAddRes]
  simp only [interpretOpList', interpretOp, VariableState.getOperandValues]
  simp only [bind, pure]
  simp_getset
  simp only [↓reduceIte, List.mapM_toArray, List.mapM_nil, Option.pure_def, Option.map_eq_map,
    Option.map_some]

  have newOpType : newOp.getOpType! newCtx.raw = .arith .constant := by grind
  rw [newOpType]
  simp only [OperationPtr.getProperties!_WfRewriter_createOp hNewCtx, ↓reduceIte]

  clear hpattern

  -- unfolding interpretOp'
  unfold interpretOp'
  simp only
  unfold Arith.interpretOp'
  simp [Interp, bind, pure]
  constructor; sorry -- Missing info from somewhere, should be easy to grab
  simp only [VariableState.getVar?_setResultValues]
  simp only [OperationPtr.getResult_op, OperationPtr.getResult_index, true_and, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_zero]
  simp only [show newOp.getNumResults! newCtx.raw = 1 by grind]
  simp

  have hnsw : properties.nsw = false := by grind
  have hnuw : properties.nuw = false := by grind

  -- Actual proof
  simp [Data.LLVM.Int.add, bind, Id.run, hnsw, hnuw]
  simp [←BitVec.toInt_inj]

open Lean Meta Elab Tactic in
/-- Search the local context for a hypothesis `interpretOp ctx op state = some (newState, cf)`
    where `op` matches `opFVarId`. Returns the `FVarId` of the hypothesis so callers can use
    it programmatically inside other `elab` tactics.
    If no such hypothesis is found, falls back to finding a `state.EquationLemmaAt ctx ...`
    hypothesis, calling it with `op (by grind) (by sorry) (by grind)`, and returning the
    resulting `state.EquationHolds ctx op` hypothesis. -/
def findInterpHypFVar (opFVarId : FVarId) : TacticM FVarId := withMainContext do
  let lctx ← getLCtx
  for ldecl in lctx do
    let ty := ldecl.type
    if !ty.isAppOfArity `Eq 3 then continue
    let eqLhs := ty.appFn!.appArg!
    let fn := eqLhs.getAppFn
    unless fn.isConst && fn.constName! == `Veir.interpretOp do continue
    unless eqLhs.getAppArgs.any (fun a => a.isFVar && a.fvarId! == opFVarId) do continue
    return ldecl.fvarId
  -- Fallback: find a `state.EquationLemmaAt ctx ...` hypothesis and call it to derive EquationHolds
  let mut eqLemmaFvar? : Option FVarId := none
  for ldecl in lctx do
    let fn := ldecl.type.getAppFn
    unless fn.isConst && fn.constName! == `Veir.InterpreterState.EquationLemmaAt do continue
    eqLemmaFvar? := some ldecl.fvarId
    break
  let some eqLemmaFvar := eqLemmaFvar? |
    throwError "findInterpHyp: no hypothesis of the form 'interpretOp ctx op state = some ...' or 'state.EquationLemmaAt ctx ...'"
  let eqLemmaIdent := mkIdent (← eqLemmaFvar.getUserName)
  let opIdent := mkIdent (← opFVarId.getUserName)
  let freshHoldsName ← mkFreshUserName `hEquationHolds
  let holdsIdent := mkIdent freshHoldsName
  let freshInterpName ← mkFreshUserName `hInterpEq
  let interpIdent := mkIdent freshInterpName
  evalTactic (← `(tactic|
    ( have $holdsIdent := $eqLemmaIdent $opIdent (by grind) (by sorry) (by grind)
      obtain ⟨_, $interpIdent⟩ := $holdsIdent )
  ))
  withMainContext do
    let lctx ← getLCtx
    for ldecl in lctx do
      if ldecl.userName == freshInterpName then
        return ldecl.fvarId
    throwError "findInterpHyp: failed to introduce interpretOp equation from EquationLemmaAt"

open Lean Meta Elab Tactic in
/-- Convenience wrapper: elaborates `opSyntax` as a local variable and returns the `ident` of the
    matching `interpretOp` hypothesis. Usable directly inside `elab` tactic handlers. -/
def findInterpHypIdent (opSyntax : TSyntax `ident) : TacticM (TSyntax `ident) :=
  withMainContext do
    let opExpr ← Elab.Tactic.elabTerm opSyntax none
    unless opExpr.isFVar do
      throwErrorAt opSyntax "expected a local variable"
    let fvar ← findInterpHypFVar opExpr.fvarId!
    withMainContext do
      return mkIdent (← fvar.getUserName)

open Lean Meta Elab Tactic in
elab "substOpResult" opName:ident : tactic => withMainContext do
  -- Elaborate opName to get the fvar for e.g. lhsOp
  let opExpr ← Elab.Tactic.elabTerm opName none
  unless opExpr.isFVar do
    throwErrorAt opName "substOpResult: expected a local variable"
  let opFVarId := opExpr.fvarId!
  let lctx ← getLCtx
  -- Search for a hypothesis `lhs.getDefiningOp! ... = some lhsOp`
  let mut lhsName? : Option Name := none
  for ldecl in lctx do
    let ty := ldecl.type
    if !ty.isAppOfArity `Eq 3 then continue
    let eqLhs := ty.appFn!.appArg!
    let eqRhs := ty.appArg!
    if !eqRhs.isAppOfArity `Option.some 2 then continue
    if eqRhs.appArg!.fvarId? != some opFVarId then continue
    let fn := eqLhs.getAppFn
    if !fn.isConst then continue
    let isGetDefiningOp := match fn.constName! with | .str _ s => s.startsWith "getDefiningOp" | _ => false
    if !isGetDefiningOp then continue
    -- Find the ValuePtr fvar among the args of getDefiningOp
    let mut foundLhs? : Option Expr := none
    for arg in eqLhs.getAppArgs do
      if !arg.isFVar then continue
      let argTy ← inferType arg
      if let some (.str _ "ValuePtr") := argTy.getAppFn.constName? then
        foundLhs? := some arg
        break
    let some lhsArg := foundLhs? | continue
    let some lhsDecl := lctx.find? lhsArg.fvarId! | continue
    lhsName? := some lhsDecl.userName
    break
  let lhsName ← match lhsName? with
    | some n => pure n
    | none => throwError "substOpResult: no hypothesis of the form 'lhs.getDefiningOp! ... = some {opName.getId}'"
  let lhsIdent := mkIdent lhsName
  let opGetResult ← `($(opName).getResult 0)
  evalTactic (← `(tactic| (
    have : $lhsIdent = ValuePtr.opResult $opGetResult := by grind
    subst this
  )))

open Lean Meta Elab Tactic in
elab "peelMatchAddi" suffix:str op:ident hpattern:ident ctx:ident bwName:ident bwVal:("(" term ")")? : tactic => do
  let suffix := suffix.getString
  let mk (base : String) : TSyntax `ident := mkIdent (.mkSimple (base ++ suffix))
  let bwExpr : TSyntax `term ← match bwVal with
    | none => `($(mk "intType").bitwidth)
    | some val => pure (⟨val.raw[1]⟩ : TSyntax `term)
  let interpHypIdent ← findInterpHypIdent op
  evalTactic (← `(tactic|
    ( /- First, grab the new variables from the pattern -/
     try simp only [Option.bind_eq_some_iff] at $hpattern:ident
     have ⟨⟨$(mk "lhs"), $(mk "rhs"), $(mk "properties")⟩, $(mk "matchAdd"), pat'⟩ := $hpattern
     clear $hpattern; have $hpattern := pat'; clear pat'
     /- Get the information gathered from `matchAddi` and verification of the op -/
     have ⟨_, _, _, _, _, _⟩ := matchAddi_implies $(mk "matchAdd")
     have : ($op:ident).Verified $ctx:ident := by grind
     have ⟨_, _, _, _, $(mk "intType"), ⟨_, _, _⟩⟩ := OperationPtr.Verified.arith_addi this (by grind)
     try substOpResult $op:ident
     let $bwName:ident := $bwExpr
     have ⟨$(mk "intLhs"), $(mk "intRhs"), $(mk "hIntLhs"), $(mk "hIntRhs"), $(mk "hAddRes"), $(mk "hCf")⟩ :=
       matchAddi_interpretOp_unfold (by grind) $(mk "matchAdd") $interpHypIdent $bwName:ident (by grind) (by grind [cases IntegerType])
     subst $(mk "hCf")
     simp only at $hpattern:ident
     )))

open Lean Meta Elab Tactic in
elab "peelMatchConstantOp" suffix:str op:ident hpattern:ident ctx:ident bwVal:term : tactic => do
  let suffix := suffix.getString
  let mk (base : String) : TSyntax `ident := mkIdent (.mkSimple (base ++ suffix))
  let bwExpr : TSyntax `term := bwVal
  let interpHypIdent ← findInterpHypIdent op
  evalTactic (← `(tactic|
    ( try simp only [Option.bind_eq_some_iff] at $hpattern:ident
      have ⟨$(mk "const"), $(mk "match"), pat'⟩ := $hpattern; clear $hpattern; have $hpattern := pat'; clear pat'
      have ⟨_, _, _, _⟩ := matchConstantOp_implies $(mk "match")
      have : ($op:ident).Verified $ctx:ident := by grind
      have ⟨_, _, _, _, _⟩ := OperationPtr.Verified.arith_constant this (by grind)
      try substOpResult $op:ident
      have ⟨$(mk "hRes"), $(mk "hCf")⟩ := matchConstantOp_interpretOp_unfold' (by grind) $(mk "match") $interpHypIdent $bwExpr (by grind)
      subst $(mk "hCf")
    )))

open Lean in
macro "peelGetDefiningOp" opName:ident hOpName:ident hpattern:ident : tactic =>
  `(tactic| (
      try simp only [Option.bind_eq_some_iff] at $hpattern:ident
      have ⟨$opName, $hOpName, pat'⟩ := $hpattern:ident
      clear $hpattern:ident; have $hpattern:ident := pat'; clear pat'
     ))

open Lean in
macro "peelSplittableCondition" "[" hyps:binderIdent* "]" hpattern:ident : tactic =>
  `(tactic| (
      split at $hpattern:ident; grind; rename_i $[$hyps]*
      try simp at $hpattern:ident
     ))

open Lean in
macro "peelSplittableCondition'" "[" hyps:binderIdent* "]" hpattern:ident : tactic =>
  `(tactic| (
      split at $hpattern:ident; rotate_left; grind; rename_i $[$hyps]*
      try simp at $hpattern:ident
     ))

open Lean in
macro "cleanupHpattern" hpattern:ident : tactic =>
  `(tactic| (
      simp at $hpattern:ident; have ⟨ha, hb, hc⟩ := $hpattern:ident; clear $hpattern:ident
      subst ha hb hc
     ))

open Lean in
macro "peelOpCreation" hpattern:ident newCtx:ident newOp:ident hNewCtx:ident : tactic =>
  `(tactic| (
      try simp only [Option.bind_eq_some_iff] at $hpattern:ident
      have ⟨⟨$newCtx, $newOp⟩, $hNewCtx, pat'⟩ := $hpattern:ident
      clear $hpattern:ident; have $hpattern:ident := pat'; clear pat'
     ))

theorem addIConstantFolding_preservesSemantics_peel :
    LocalRewritePattern.PreservesSemantics addIConstantFolding h := by
  -- Unfold definition and cleanup hypotheses
  simp only [LocalRewritePattern.PreservesSemantics, addIConstantFolding]
  intros ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp only [Option.bind_eq_bind] at hpattern

  -- Process hpattern
  peelMatchAddi "" op hpattern ctx bw
  peelSplittableCondition [hproperties] hpattern
  peelGetDefiningOp lhsOp hLhsOp hpattern
  peelGetDefiningOp rhsOp hRhsOp hpattern
  peelMatchConstantOp "Lhs" lhsOp hpattern ctx bw
  peelMatchConstantOp "Rhs" rhsOp hpattern ctx bw
  peelSplittableCondition' [intType' _ _] hpattern
  peelOpCreation hpattern newCtx newOp hNewCtx
  cleanupHpattern hpattern

  -- Plug input/output information between match instructions
  simp [hIntLhs] at hResLhs
  simp [hIntRhs] at hResRhs
  subst intLhs intRhs

  -- Resolve the new state values
  simp [hAddRes]
  simp [interpretOpList', interpretOp, VariableState.getOperandValues, bind, pure]
  simp_getset; simp
  rw [show newOp.getOpType! newCtx.raw = .arith .constant by grind]
  simp_getset; simp
  clear hpattern

  -- unfolding interpretOp'
  unfold interpretOp'; simp only; unfold Arith.interpretOp'; simp only
  simp [Interp, bind, pure, liftM, monadLift, MonadLift.monadLift]
  constructor; sorry -- Missing info from somewhere, should be easy to grab
  simp [VariableState.getVar?_setResultValues]
  simp_getset; simp

  simp [show properties.nsw = false by grind, show properties.nuw = false by grind]

  -- Actual proof
  have : intType = intType' := by grind
  subst intType'
  simp [Data.LLVM.Int.add, bind, Id.run, ←BitVec.toInt_inj, bw]


def addIComm (ctx: WfIRContext OpCode) (op: OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  -- Match an `arith.addi`
  let (lhs, rhs, addProp) ← matchAddi op ctx

  -- Commutes it
  let ⟨.integerType intType, _⟩ := (lhs.getType! ctx.raw) | none
  let (ctx, newOp) ← WfRewriter.createOp ctx (.arith .addi) #[intType] #[rhs, lhs] #[] #[] addProp none sorry sorry sorry sorry
  return (ctx, some (#[newOp], #[newOp.getResult 0]))

theorem addIComm_preservesSemantics :
    LocalRewritePattern.PreservesSemantics addIComm h := by
  -- Unfold definition and cleanup hypotheses
  simp only [LocalRewritePattern.PreservesSemantics, addIComm]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp only [Option.bind_eq_bind] at hpattern

  peelMatchAddi "" op hpattern ctx bw
  peelSplittableCondition' [intType' _ _] hpattern
  peelOpCreation hpattern newCtx newOp hNewCtx
  cleanupHpattern hpattern

  -- Resolve the new state values
  simp [hAddRes]
  simp [interpretOpList', interpretOp, VariableState.getOperandValues]
  simp_getset; simp
  simp [hIntLhs, hIntRhs]
  rw [show newOp.getOpType! newCtx.raw = .arith .addi by grind]
  unfold interpretOp'; simp only; unfold Arith.interpretOp'; simp only
  simp [pure, Interp, bind, liftM, monadLift, MonadLift.monadLift]
  constructor; sorry -- Missing info from somewhere, should be easy to grab
  simp [VariableState.getVar?_setResultValues]
  simp_getset; simp

  -- Actual proof
  simp [Data.LLVM.Int.add, bind, Id.run]
  sorry -- easy lemma

def addIAssoc (ctx: WfIRContext OpCode) (op: OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  -- Match an (x + y) + z
  let (lhs, z, addProp) ← matchAddi op ctx
  if addProp.nsw || addProp.nuw then
    return (ctx, none)

  let lhsOp ← lhs.getDefiningOp! ctx.raw
  let (x, y, addProp') ← matchAddi lhsOp ctx
  if addProp'.nsw || addProp'.nuw then
    return (ctx, none)

  let ⟨.integerType intType, _⟩ := (lhs.getType! ctx.raw) | none
  -- Create (y + z)
  let (ctx, newOp) ← WfRewriter.createOp ctx (.arith .addi) #[intType] #[y, z] #[] #[] addProp none sorry sorry sorry sorry
  -- Create x + (y + z)
  let (ctx, newOp') ← WfRewriter.createOp ctx (.arith .addi) #[intType] #[x, newOp.getResult 0] #[] #[] addProp' none sorry sorry sorry sorry
  return (ctx, some (#[newOp, newOp'], #[newOp'.getResult 0]))

theorem addIAssoc_preservesSemantics :
    LocalRewritePattern.PreservesSemantics addIAssoc h := by
  -- Unfold definition and cleanup hypotheses
  simp only [LocalRewritePattern.PreservesSemantics, addIAssoc]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp only [Option.bind_eq_bind] at hpattern

  peelMatchAddi "" op hpattern ctx bw
  peelSplittableCondition [hproperties] hpattern
  peelGetDefiningOp lhsOp hLhsOp hpattern
  peelMatchAddi "Lhs" lhsOp hpattern ctx bw'
  peelSplittableCondition [hproperties'] hpattern
  peelSplittableCondition' [intType' _ _] hpattern
  peelOpCreation hpattern newCtx newOp hNewCtx
  peelOpCreation hpattern newCtx' newOp' hNewCtx'
  cleanupHpattern hpattern

  have : bw = bw' := by grind
  subst bw
  subst bw'

  simp [*]
  have : intType = intTypeLhs := by grind
  subst intTypeLhs
  simp [hIntLhs] at hAddResLhs; subst hAddResLhs

  simp [interpretOpList', interpretOp, VariableState.getOperandValues]
  simp_getset; simp
  have : newOp ≠ newOp' := by sorry -- interesting, should be easy to prove somehow
  simp [this]
  have : newOp' ≠ newOp := by grind
  simp [*]
  simp [interpretOp']
  rw [show newOp.getOpType! newCtx'.raw = .arith .addi by grind]
  rw [show newOp'.getOpType! newCtx'.raw = .arith .addi by grind]
  simp
  unfold Arith.interpretOp'; simp
  simp [Interp, pure, bind]
  have : lhsLhs ∉ newOp.getResults! newCtx'.raw := by sorry
  simp [VariableState.getVar?_setResultValues' this]
  simp [*]
  simp [VariableState.getVar?_setResultValues]
  simp_getset
  simp [liftM, monadLift, MonadLift.monadLift]
  constructor; sorry

  grind
