// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Tier 2 telescoping rewrites:
//   (x + c) - c -> x    (add_sub_const_cancel)
//   (x - c) + c -> x    (sub_add_const_cancel)
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type, %anchor: !felt.type):
  %c5 = "felt.const"() <{"value" = #felt<const 5> : !felt.type}> : () -> !felt.type
  // (a + 5) - 5 -> a
  %a_plus  = "felt.add"(%a, %c5) : (!felt.type, !felt.type) -> !felt.type
  %t1      = "felt.sub"(%a_plus, %c5) : (!felt.type, !felt.type) -> !felt.type
  // (b - 5) + 5 -> b
  %b_minus = "felt.sub"(%b, %c5) : (!felt.type, !felt.type) -> !felt.type
  %t2      = "felt.add"(%b_minus, %c5) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%t1, %anchor) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%t2, %anchor) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// Both telescoped pairs collapse to their block arguments, leaving the
// inner add/sub and the shared constant dead; the driver erases them, so
// no felt arithmetic survives at all.
//
// CHECK:        "builtin.module"() ({
// CHECK-NEXT:     ^{{.*}}:
// CHECK-NEXT:     "constrain.eq"({{.*}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:     "constrain.eq"({{.*}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:   }) : () -> ()
