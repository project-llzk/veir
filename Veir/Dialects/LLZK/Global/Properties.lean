module

public import Veir.IR.Attribute
public import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/--
  Properties of the `global.def` operation.

  - `sym_name`: the global's name. **Stored as `StringAttr`**, matching
    LLZK's `SymbolNameAttr` (a `StringAttr` constraint). Generic-form
    printing: `<{sym_name = "counter", ...}>`. This is the *producer*
    side of a symbol; the `@`-prefix form is only for users (see
    `global.read`/`global.write`'s `name_ref` field below).
  - `constant`: presence of the `const` modifier (LLZK's `UnitAttr:$constant`).
  - `type`: the global's declared type. Stored as `Attribute` (not `TypeAttr`)
    because VEIR's per-op properties don't currently carry the `isType`
    refinement; consumers of `type` should treat it as a type attribute
    and pattern-match accordingly. **Not validated** — we don't enforce
    that the attribute is a type; this is a coverage gap (see
    `harness/coverage.md` §Op-level features).
  - `initial_value`: optional initial value. Any `Attribute` is accepted
    (LLZK uses `DefaultValuedAttr<AnyAttr, "nullptr">`). **Not validated**
    against `type`.

  Caveats:
  - `HasParent<ModuleOp>` trait not encoded — VEIR will accept
    `global.def` anywhere, not just directly under `builtin.module`.
  - `Symbol` trait not encoded — no uniqueness invariant on `sym_name`.
  - `SymbolUserOpInterface` not encoded — `global.read`/`global.write`
    references are not validated against existing `global.def`s.
-/
structure GlobalDefProperties where
  sym_name : StringAttr
  constant : Bool
  type : Attribute
  initial_value : Option Attribute
deriving Inhabited, Repr, Hashable, DecidableEq

def GlobalDefProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String GlobalDefProperties := do
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw "global.def: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"global.def: expected 'sym_name' to be a string attribute, got {symAttr}"
  let constant ← getUnitAttr "constant" attrDict
  let some typeAttr := attrDict["type".toUTF8]?
    | throw "global.def: missing 'type' property"
  let initial_value := attrDict["initial_value".toUTF8]?
  -- Reject unrecognized keys.
  let expected := 2 + (if constant then 1 else 0) + (if initial_value.isSome then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"global.def: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { sym_name := sym, constant := constant, type := typeAttr, initial_value := initial_value }

/--
  Properties of the `global.read` and `global.write` operations.

  Both ops carry a single `name_ref` attribute that points at the
  `global.def` they target. Stored as `FlatSymbolRefAttr`; nested
  `@A::@B` paths are not supported (Phase F).
-/
structure GlobalRefProperties where
  name_ref : FlatSymbolRefAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def GlobalRefProperties.fromAttrDict (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String GlobalRefProperties := do
  if attrDict.size > 1 then
    throw s!"{opName}: expected only 'name_ref' property, got {attrDict.size} properties"
  let some refAttr := attrDict["name_ref".toUTF8]?
    | throw s!"{opName}: missing 'name_ref' property"
  let .flatSymbolRefAttr ref := refAttr
    | throw s!"{opName}: expected 'name_ref' to be a flat symbol ref, got {refAttr}"
  return { name_ref := ref }

end

end Veir
