// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.add x (felt.neg x) -> felt.const 0.  Soundness: add_neg_to_zero.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%a: !felt.type, %anchor: !felt.type):
  %na = "felt.neg"(%a) : (!felt.type) -> !felt.type
  %r = "felt.add"(%a, %na) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%r, %anchor) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// The add collapses to a const 0, which the constrain then consumes; the
// neg is dead afterwards and the driver erases it.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %[[Z:[^ ]+]] = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:     "constrain.eq"(%[[Z]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NOT:    "felt.add"
// CHECK-NOT:    "felt.neg"
