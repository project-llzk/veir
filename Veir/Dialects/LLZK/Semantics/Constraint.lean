module

public import Mathlib.Data.ZMod.Basic
public import Veir.IR.Basic
public import Veir.OpCode

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
def FeltExpr.eval {p : Nat} (σ : Assignment p) : FeltExpr → ZMod p :=
  sorry

/-- **Exercise A2.** Adding a zero constant changes nothing, in every modulus.
    This is the first of the 15 `felt-combine` identities, at the value level. -/
theorem eval_add_const_zero {p : Nat} (σ : Assignment p) (e : FeltExpr) :
    (FeltExpr.add e (FeltExpr.const 0)).eval σ = e.eval σ :=
  sorry

/-- **Exercise A3.** Constant folding is modulus-independent, because `const` is
    a ring hom. This is the theorem behind the claim that VeIR can fold on bare
    `!felt.type` where the C++ folder declines to. -/
theorem eval_const_add {p : Nat} (σ : Assignment p) (a b : Int) :
    (FeltExpr.add (FeltExpr.const a) (FeltExpr.const b)).eval σ
      = (FeltExpr.const (a + b)).eval σ :=
  sorry

/-! ## Part B — walking real IR -/

/-- The value environment: what each SSA value evaluates to. Note this maps
    `ValuePtr`, not `Signal` — most values are *computed*, not assigned. -/
abbrev ValEnv (p : Nat) := Std.HashMap ValuePtr (ZMod p)

/-- **Exercise B1.** Collect the operations of a block into a list, in order.

    Hint: start at `blk.firstOp! ctx` and follow `op.next! ctx` until `none`.
    Use `Id.run do` with `let mut`, the way `Veir/Passes/CSE.lean` does.
    Lean needs to see this terminates — `partial def` is the pragmatic escape
    if the structure fights you. -/
def opsOf (ctx : IRContext OpCode) (blk : BlockPtr) : List OperationPtr :=
  sorry

/-- **Exercise B2.** Evaluate one field-native felt operation, given values for
    its operands. Return `none` for anything outside the modelled fragment.

    Cases to handle: `.felt .const`, `.felt .add`, `.felt .sub`, `.felt .mul`,
    `.felt .neg`. Everything else is `none`.

    Hints:
    - `op.getOpType! ctx` gives the `OpCode`
    - `op.getOperands! ctx` gives an `Array ValuePtr`
    - `op.getProperties! ctx _` gives the typed properties; for `felt.const`
      that is `FeltConstProperties`, whose `.value` is an `Int`
    - `env[v]?` looks up a `ValuePtr` -/
def evalFeltOp {p : Nat} (ctx : IRContext OpCode) (op : OperationPtr)
    (env : ValEnv p) : Option (ZMod p) :=
  sorry

/-- **Exercise B3.** Seed the environment from the block's felt arguments:
    argument `i` gets the value `σ i`. -/
def seedBlockArgs {p : Nat} (ctx : IRContext OpCode) (blk : BlockPtr)
    (σ : Assignment p) : ValEnv p :=
  sorry

/-- **Exercise B4.** Walk the body: felt ops extend the environment, each
    `constrain.eq` contributes a pair of values that must agree.
    Return `none` if any op is outside the modelled fragment. -/
def evalBody {p : Nat} (ctx : IRContext OpCode) (blk : BlockPtr)
    (env₀ : ValEnv p) : Option (ValEnv p × List (ZMod p × ZMod p)) :=
  sorry

/-! ## Part C — satisfaction -/

/-- **Exercise C1.** The proposition: under `σ`, every constraint holds. -/
def IRSat {p : Nat} (ctx : IRContext OpCode) (blk : BlockPtr)
    (σ : Assignment p) : Prop :=
  sorry

/-- **Exercise C2.** The executable twin, for `#eval` tests. -/
def irsatb {p : Nat} (ctx : IRContext OpCode) (blk : BlockPtr)
    (σ : Assignment p) : Bool :=
  sorry

/-- **Exercise C3.** The two agree. If this is painful, the definitions of
    `IRSat` and `irsatb` have drifted apart — make them structurally parallel
    and it should fall to `simp`. -/
theorem irsatb_iff_IRSat {p : Nat} (ctx : IRContext OpCode) (blk : BlockPtr)
    (σ : Assignment p) : irsatb ctx blk σ = true ↔ IRSat ctx blk σ :=
  sorry

end

end Veir.LLZK.Semantics
