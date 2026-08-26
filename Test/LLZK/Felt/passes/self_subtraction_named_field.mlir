// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Regression test for the post-2026-05-17 audit's Real Issue #3:
// self_subtraction_to_zero was hard-coding `fieldType := { fieldName := none }`
// for the synthesized felt.const. On named-field felt (here, "bn254"),
// that produced `<{value = #felt<const 0> : !felt.type}> : () -> !felt.type<"bn254">`
// — a type mismatch between attribute fieldType and op result type that
// LLZK's verifier would reject. Fix: extract fieldType from the
// operand's actual type before synthesis.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%x: !felt.type<"bn254">, %anchor: !felt.type<"bn254">):
  %s = "felt.sub"(%x, %x) : (!felt.type<"bn254">, !felt.type<"bn254">) -> !felt.type<"bn254">
  "constrain.eq"(%s, %anchor) : (!felt.type<"bn254">, !felt.type<"bn254">) -> ()
}) : () -> ()

// CHECK: %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 0> : !felt.type<"bn254">}> : () -> !felt.type<"bn254">
