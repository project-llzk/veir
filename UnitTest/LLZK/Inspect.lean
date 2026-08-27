import Veir.Parser.MlirParser
import Veir.Printer
import Veir.GlobalOpInfo

open Veir
open Veir.Parser

/-- A minimal LLZK constrain body: `a*b + 3 = a`, asserted twice. -/
def sample : String := r#""builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %0 = "felt.mul"(%a, %b) : (!felt.type, !felt.type) -> !felt.type
  %1 = "felt.const"() <{"value" = #felt<const 3> : !felt.type}> : () -> !felt.type
  %2 = "felt.add"(%0, %1) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%2, %a) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%2, %a) : (!felt.type, !felt.type) -> ()
}) : () -> ()"#

def roundTrip (s : String) : IO Unit :=
  match WfIRContext.create OpCode with
  | none => IO.println "internal error: failed to create IR context"
  | some (ctx, _) =>
    match ParserState.fromInput s.toByteArray with
    | .error e => IO.println s!"lex error: {e}"
    | .ok parser =>
      match parseTopLevelOp.run (MlirParserState.fromContext ctx) parser with
      | .ok (op, st, _) => Printer.printOperation st.ctx.raw op
      | .error e => IO.println s!"parse error: {e}"

def inspect (s : String) : IO Unit := do
  let some (ctx, _) := WfIRContext.create OpCode | IO.println "no ctx"
  let .ok parser := ParserState.fromInput s.toByteArray | IO.println "lex failed"
  let .ok (top, st, _) := parseTopLevelOp.run (MlirParserState.fromContext ctx) parser | IO.println "parse failed"
  let c := st.ctx.raw

  for region in (top.get! c).regions do
    let mut blk := (region.get! c).firstBlock
    while let some b := blk do
      let mut op := (b.get! c).firstOp
      while let some o := op do
        IO.println s!"op type: {repr (o.getOpType! c)}"
        IO.println s!"op arg cnt: {(o.getNumOperands! c)}"
        op := (o.get! c).next
      blk := (b.get! c).next

-- #eval inspect sample
