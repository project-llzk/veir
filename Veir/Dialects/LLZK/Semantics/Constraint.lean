module

public import Mathlib.Data.ZMod.Basic
public import Veir.IR.Basic
public import Veir.GlobalOpInfo

/-!
# LLZK constraint semantics

What an LLZK `constrain` body *means*: a predicate over assignments to signals.

VeIR's built-in semantics is entirely operational (`interpretOp'`,
`InterpreterState`) — it models ops that *compute* a value. `constrain.eq` has
zero results; it *asserts*. So there is nothing to reuse here, and this file
supplies the declarative counterpart.

Everything is parameterised by the modulus `p` and proofs are `∀ p`. No field
registry is needed: `typesUnify` has no `FeltType` case, so the verifier already
guarantees a uniform field across any connected expression.

**This file is an exercise skeleton.** See `EXERCISES.md`. Each `sorry` is a
numbered exercise; signatures are given, bodies are yours.
-/

namespace Veir.LLZK.Semantics

public section

/-! ## Part A — warm-up, no IR involved -/

/-- A signal: a free variable of the constraint system. Concretely a felt block
    argument, or (later) a `struct.readm` of a member. -/
abbrev Signal := Nat

/-- An assignment of field elements to signals. -/
abbrev Assignment (p : Nat) := Signal → ZMod p

/-- A tree-shaped felt expression. Used only for the warm-up exercises; the real
    representation is the SSA graph in the IR, which preserves sharing. -/
inductive FeltExpr where
  | sig   (s : Signal)
  | const (n : Int)
  | add   (a b : FeltExpr)
  | mul   (a b : FeltExpr)
  | neg   (a : FeltExpr)
deriving Repr, DecidableEq, Inhabited

/-- **Exercise A1.** Evaluate an expression under an assignment.
    `const` should be `Int.cast` — the ring hom `ℤ → ZMod p`. Do not reduce; that
    would need a concrete modulus and is not required for correctness. -/
@[grind]
def FeltExpr.eval {p : Nat} (σ : Assignment p) : FeltExpr → ZMod p :=
  fun e => match e with
    | .sig s => σ s
    | .const n => (n : ZMod p)
    | .add a b => a.eval σ  + b.eval σ
    | .mul a b => a.eval σ  * b.eval σ
    | .neg a => - a.eval σ

/-- **Exercise A2.** Adding a zero constant changes nothing, in every modulus.
    This is the first of the 15 `felt-combine` identities, at the value level. -/
theorem eval_add_const_zero {p : Nat} (σ : Assignment p) (e : FeltExpr) :
    (FeltExpr.add e (FeltExpr.const 0)).eval σ = e.eval σ := by
    grind

/-- **Exercise A3.** Constant folding is modulus-independent, because `const` is
    a ring hom. This is the theorem behind the claim that VeIR can fold on bare
    `!felt.type` where the C++ folder declines to. -/
theorem eval_const_add {p : Nat} (σ : Assignment p) (a b : Int) :
    (FeltExpr.add (FeltExpr.const a) (FeltExpr.const b)).eval σ
      = (FeltExpr.const (a + b)).eval σ := by
  simp only [FeltExpr.eval, Int.cast_add]



/-! ## Part B — walking real IR -/

/-- The value environment: what each SSA value evaluates to. Note this maps
    `ValuePtr`, not `Signal` — most values are *computed*, not assigned. -/
abbrev ValEnv (p : Nat) := Std.HashMap ValuePtr (ZMod p)

/-- **Exercise B1.** Collect the operations of a block into a list, in order.

    Hint: start at `(blk.get! ctx).firstOp` and follow `(op.get! ctx).next`
    until `none`. (There is no `firstOp!`/`next!` — dereference, then read the
    field.) Use `Id.run do` with `let mut`, as `Veir/Passes/CSE.lean` does.

    This is the **executable** track. The `while` compiles to a partial fixpoint
    over `Loop`, so it runs but cannot be unfolded in a proof — `simp [opsOf]`
    leaves an unusable goal about `forIn` membership. The proof-side twin is
    `BlockPtr.operationList` (`Veir/IR/WellFormed.lean:867`), which is
    `noncomputable` and takes its list from `ctx.WellFormed`'s `opChain`
    existential. Same split as `interpretOpChain` vs `interpretOpList`. -/

def op_chain (ctx : WfIRContext OpCode) (op: OperationPtr) (hop : op.InBounds ctx.raw := by grind) : List OperationPtr :=
  match h: (op.get ctx.raw).next with
  | none => [op]
  | some next => op :: op_chain ctx next
termination_by op.idxInParentFromTail ctx.raw
decreasing_by grind

def opsOf (ctx : WfIRContext OpCode) (blk : BlockPtr) (hblk: blk.InBounds ctx.raw := by grind) : List OperationPtr :=
  match h : (blk.get! ctx.raw).firstOp with
  | none => []
  | some op => op_chain ctx op

/-- **Exercise B2.** Evaluate one field-native felt operation, given values for
    its operands. Return `none` for anything outside the modelled fragment.

    Cases to handle: `.felt .const`, `.felt .add`, `.felt .sub`, `.felt .mul`,
    `.felt .neg`. Everything else is `none`.

    Hints:
    - `op.getOpType! ctx` gives the `OpCode`
    - `op.getOperands! ctx` gives an `Array ValuePtr`
    - `op.getProperties! ctx <opcode>` gives the typed properties; the return
      type *depends on* the opcode you pass, so you must supply it in full
      (`OpCode.felt Felt.const` — dotted `.felt .const` cannot be resolved
      there). For `felt.const` that is `FeltConstProperties`, whose `.value` is
      a `FeltConstAttr`, whose `.value` is the `Int`. Two hops.
    - `env[v]?` looks up a `ValuePtr`; operand indices are 0-based -/
def evalFeltOp {p : Nat} (ctx : IRContext OpCode) (op : OperationPtr)
    (env : ValEnv p) : Option (ZMod p) :=
  match op.getOpType! ctx with
  | .felt .const => some (op.getProperties! ctx (OpCode.felt Felt.const)).value.value
  | .felt .add => do return (← env[op.getOperand! ctx 0]?) + (← env[op.getOperand! ctx 1]?)
  | .felt .sub => do return (← env[op.getOperand! ctx 0]?) - (← env[op.getOperand! ctx 1]?)
  | .felt .mul => do return (← env[op.getOperand! ctx 0]?) * (← env[op.getOperand! ctx 1]?)
  | .felt .neg => do return -(← env[op.getOperand! ctx 0]?)
  | _ => none


/-- **Exercise B3.** Seed the environment from the block's felt arguments:
    argument `i` gets the value `σ i`. -/
def seedBlockArgs {p : Nat} (ctx : IRContext OpCode) (blk : BlockPtr)
  (σ : Assignment p) : ValEnv p := Id.run do
  let args := blk.getArguments! ctx
  let mut valenv := Std.HashMap.emptyWithCapacity
  for h: i in [0:args.size] do
    let argi := args[i]
    let argiType := (argi.getType! ctx).val
    match argiType with
    | .feltType _ => valenv := valenv.insert argi (σ i)
    | _ => continue

  valenv


/-- **Exercise B4.** Walk the body: felt ops extend the environment, each
    `constrain.eq` contributes a pair of values that must agree.
    Return `none` if any op is outside the modelled fragment.

    **Signature changed 2026-08-27**: takes `ops : List OperationPtr`, not a
    `BlockPtr`. Taking a block would force this to walk it internally via
    `opsOf`, and `IRSat` (built on top) would inherit that walk's opacity —
    Part E would then arrive at an unprovable goal. Taking the list makes this
    plain structural recursion: executable *and* provable, with real equation
    lemmas. All the opacity is quarantined in the single choice of *which* list
    gets passed in. `Veir/Interpreter/Basic.lean:1754` (`interpretOpList`) has
    the same signature for the same reason.

    Dispatch three ways, and check `constrain.eq` *before* calling
    `evalFeltOp` — that returns `none` both for "outside the fragment" and for
    "in the fragment but produces no value", and `constrain.eq` is the latter. -/
@[expose]
def evalBody {p : Nat} (ctx : IRContext OpCode) (ops : List OperationPtr)
    (env₀ : ValEnv p) : Option (ValEnv p × List (ZMod p × ZMod p)) :=
  match ops with
  | [] => some (env₀, [])
  | op :: ops =>
    match op.getOpType! ctx with
    | .constrain .eq => do
      let lhs ← env₀[op.getOperand! ctx 0]?
      let rhs ← env₀[op.getOperand! ctx 1]?
      let (env, cs) ← evalBody ctx ops env₀
      return (env, (lhs, rhs) :: cs)
    | _ => do
      let v ← evalFeltOp ctx op env₀
      evalBody ctx ops (env₀.insert (op.getResult 0) v)

/-! ## Part C — satisfaction -/

/-- **Exercise C1.** The proposition: under `σ`, every constraint holds.

    Feed `evalBody` the **proof-side** list: `(blk.operationList ctx).toList`.
    Both of `operationList`'s proof arguments are `by grind` auto-params, so
    `blk.operationList ctx` usually suffices. Do NOT use `opsOf` here — see B1. -/
@[grind]
def IRSat {p : Nat} (ctx : WfIRContext OpCode) (blk : BlockPtr) (hBlock: blk.InBounds ctx.raw := by grind)
    (σ : Assignment p) : Prop :=
  match evalBody ctx (blk.operationList ctx.raw).toList (seedBlockArgs ctx blk σ) with
  | none => False
  | some (e, c) => ∀ (lhs rhs: ZMod p), (lhs, rhs) ∈ c → lhs = rhs

/-- **Exercise C2.** The executable twin, for `#eval` tests.

    Feed `evalBody` the **executable** list: `opsOf ctx blk`. Same `evalBody`,
    same `seedBlockArgs`; the only difference from `IRSat` is where the list
    comes from. -/
def irsatb {p : Nat} (ctx : WfIRContext OpCode) (blk : BlockPtr) (hblk: blk.InBounds ctx.raw)
    (σ : Assignment p) : Bool :=
  let r := evalBody ctx (opsOf ctx blk) (seedBlockArgs ctx blk σ)
  match r with
  | none => false
  | some (_, v) => v.all (fun (x, y) => x = y)

theorem op_chain_eq_drop (ctx : WfIRContext OpCode) (blk : BlockPtr)
    {array : Array OperationPtr} (hchain : BlockPtr.OpChain blk ctx.raw array) (n : Nat) :
    ∀ (i : Nat) (_hin : i + n = array.size) (hi : i < array.size)
      (hop : array[i].InBounds ctx.raw),
      op_chain ctx array[i] hop = array.toList.drop i := by
  induction n with
  | zero => grind
  | succ n ih =>
    intro i hin hi hop
    have hnext := hchain.next hi
    rw [op_chain]
    split
    · grind [List.drop_eq_getElem_cons]
    · grind [List.drop_eq_getElem_cons]


theorem opsOf_eq_operationList (ctx : WfIRContext OpCode) (blk : BlockPtr)
    (hBlock : blk.InBounds ctx.raw) :
    opsOf ctx blk hBlock = (blk.operationList ctx.raw).toList := by
  have hchain := BlockPtr.operationListWF ctx.raw blk hBlock ctx.wellFormed
  have hfirst := hchain.first
  have hdrop := op_chain_eq_drop ctx blk hchain (blk.operationList ctx.raw).size 0
  unfold opsOf
  split
  · grind [Array.toList_eq_nil_iff, Array.size_eq_zero_iff]
  · grind

/-- **Exercise C3.** The two agree.

    With C1/C2 as described, this reduces to a single bridge lemma —
    `opsOf ctx blk = (blk.operationList ctx).toList` — plus determinism of
    `evalBody`. That is the same bridge as
    `interpretOpChain_eq_interpretTerminatedOpList_of_firstOp`
    (`Veir/Interpreter/Lemmas.lean:625`); read that statement first.

    This will need `ctx.WellFormed` as a hypothesis: it is what guarantees the
    `next` chain is finite and acyclic, which is exactly what `opsOf`'s `while`
    assumes without proof. -/
theorem irsatb_iff_IRSat {p : Nat} (ctx : WfIRContext OpCode) (blk : BlockPtr)
    (hBlock : blk.InBounds ctx.raw) (σ : Assignment p) :
    irsatb ctx blk hBlock σ = true ↔ IRSat ctx blk hBlock σ := by
  unfold irsatb IRSat
  rw [opsOf_eq_operationList]
  split <;> simp_all


end

end Veir.LLZK.Semantics
