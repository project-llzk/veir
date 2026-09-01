module

public import Veir.IR.Attribute
public import Veir.IR.OpInfo

namespace Veir

public section

/--
  Properties of the `bool.assert` operation.

  `msg` is optional — a human-readable string emitted if the assertion fires.
  The LLZK custom assembly form is `bool.assert %cond` (no msg) or
  `bool.assert %cond, "message"`. In VEIR generic form: `<{msg = "message"}>`
  when present, absent otherwise.
-/
structure BoolAssertProperties where
  msg : Option StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def BoolAssertProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String BoolAssertProperties := do
  if attrDict.size > 1 then
    throw s!"bool.assert: expected at most 'msg' property, got {attrDict.size}"
  let msg ← match attrDict["msg".toUTF8]? with
    | some (.stringAttr m) => .ok (some m)
    | some attr => .error s!"bool.assert: expected 'msg' to be a string attribute, got {attr}"
    | none => .ok none
  -- Catch the case `size = 1` with an unrecognized key (which would otherwise
  -- silently coerce to `{ msg := none }`).
  if attrDict.size = 1 ∧ msg.isNone then
    throw "bool.assert: only 'msg' is a recognized property"
  return { msg := msg }

/--
  Properties of the `bool.cmp` operation.

  `predicate` is LLZK's `FeltCmpPredicate` enum (an `I32EnumAttr` upstream):
  `eq=0, ne=1, lt=2, le=3, gt=4, ge=5`, stored as a plain `IntegerAttr`
  with `i32` type — the IntegerAttr-as-enum workaround documented in
  `harness/porting-notes.md` (2026-05-15 enum-attr pattern).

  `enumSpelling` records how the predicate was written, so printing is
  faithful and `llzk-opt` (which only accepts the enum form) can re-ingest
  VEIR output: `none` for the integer spelling (`2 : i32`), `some withCmp`
  for the enum spellings (`#bool<lt>` / older `#bool<cmp lt>`).
-/
structure BoolCmpProperties where
  predicate : IntegerAttr
  enumSpelling : Option Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def BoolCmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String BoolCmpProperties := do
  if attrDict.size > 1 then
    throw s!"bool.cmp: expected only 'predicate' property, got {attrDict.size}"
  let some attr := attrDict["predicate".toUTF8]?
    | throw "bool.cmp: missing 'predicate' property"
  let (value, spelling) ← match attr with
    | .integerAttr intAttr => pure (intAttr, none)
    | .boolCmpPredicateAttr pred =>
      pure (({ value := pred.value, type := { bitwidth := 32 } } : IntegerAttr),
            some pred.withCmp)
    | _ =>
      throw s!"bool.cmp: expected 'predicate' to be an integer attribute or #bool<...>, got {attr}"
  if value.value < 0 ∨ value.value > 5 then
    throw s!"bool.cmp: 'predicate' must be in 0..5 (eq/ne/lt/le/gt/ge), got {value.value}"
  return { predicate := value, enumSpelling := spelling }

def BoolCmpProperties.predicateAttr (props : BoolCmpProperties) : Attribute :=
  match props.enumSpelling with
  | none => Attribute.integerAttr props.predicate
  | some withCmp =>
    Attribute.boolCmpPredicateAttr { value := props.predicate.value, withCmp }

end

end Veir
