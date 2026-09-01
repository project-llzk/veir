// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: an unrecognised mnemonic inside LLZK's `#bool<...>`
// enum spelling. The attribute parser rejects it by name, so the error
// names the six legal mnemonics rather than falling through to the
// generic "attribute is not registered" message.

// CHECK: #bool<...> expects one of eq, ne, lt, le, gt, ge
"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %x = "bool.cmp"(%a, %b) <{predicate = #bool<bogus>}> : (!felt.type, !felt.type) -> i1
}) : () -> ()
