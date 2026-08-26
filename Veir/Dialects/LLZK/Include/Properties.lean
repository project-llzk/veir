module

public import Veir.IR.Attribute
public import Veir.IR.OpInfo

namespace Veir

public section

/--
  Properties of the `include.from` operation.

  - `sym_name`: the local alias the included module is bound to. **Stored
    as `StringAttr`**, matching LLZK's `SymbolNameAttr` (which is a
    `StringAttr` constraint in ODS). In generic MLIR, this prints as
    `<{sym_name = "aliasName", ...}>` — NOT `@aliasName`. The `@`-prefix
    form is for `SymbolRefAttr` users (e.g. `global.read`'s `name_ref`),
    not Symbol producers.
  - `path`: the file path to include (e.g. `"lib.llzk"`).

  Caveat: the `Symbol` trait on `include.from` is not encoded in VEIR;
  no symbol-table lookup, no uniqueness invariant on `sym_name`.
-/
structure IncludeFromProperties where
  sym_name : StringAttr
  path : StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def IncludeFromProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String IncludeFromProperties := do
  if attrDict.size > 2 then
    throw s!"include.from: expected 'sym_name' and 'path' properties, got {attrDict.size}"
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw "include.from: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"include.from: expected 'sym_name' to be a string attribute, got {symAttr}"
  let some pathAttr := attrDict["path".toUTF8]?
    | throw "include.from: missing 'path' property"
  let .stringAttr path := pathAttr
    | throw s!"include.from: expected 'path' to be a string attribute, got {pathAttr}"
  return { sym_name := sym, path := path }

end

end Veir
