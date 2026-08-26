// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.mul x (felt.const 0) -> felt.const 0.  Soundness: right_zero_mul.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%a: !felt.type, %anchor: !felt.type):
  %z = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
  %r = "felt.mul"(%a, %z) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%r, %anchor) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// The mul collapses to a freshly synthesized const 0 that the constrain
// consumes; the original zero const is then dead and gets erased.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %[[Z:[^ ]+]] = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:     "constrain.eq"(%[[Z]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NOT:    "felt.mul"
