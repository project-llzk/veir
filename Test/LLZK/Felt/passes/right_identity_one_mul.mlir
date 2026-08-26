// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.mul x (felt.const 1) -> x.  Soundness: right_identity_one_mul.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%a: !felt.type, %anchor: !felt.type):
  %one = "felt.const"() <{"value" = #felt<const 1> : !felt.type}> : () -> !felt.type
  %r = "felt.mul"(%a, %one) : (!felt.type, !felt.type) -> !felt.type
  // Non-matching: rhs is const 2, must stay.
  %two = "felt.const"() <{"value" = #felt<const 2> : !felt.type}> : () -> !felt.type
  %s = "felt.mul"(%a, %two) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%r, %anchor) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%s, %anchor) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// The x*1 mul is replaced by the block argument (leaving `felt.const 1`
// dead, hence erased); the x*2 mul survives untouched.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %[[TWO:[^ ]+]] = "felt.const"() <{"value" = #felt<const 2> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:     %[[S:[^ ]+]] = "felt.mul"(%{{[^,]+}}, %[[TWO]]) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:     "constrain.eq"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:     "constrain.eq"(%[[S]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NOT:    #felt<const 1>
