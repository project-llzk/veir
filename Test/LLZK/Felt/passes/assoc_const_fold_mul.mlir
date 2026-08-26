// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.mul (felt.mul x c1) c2 -> felt.mul x (c1*c2).
// Soundness: assoc_const_fold_mul.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%x: !felt.type<"babybear">, %anchor: !felt.type<"babybear">):
  %c3 = "felt.const"() <{"value" = #felt<const 3> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %c4 = "felt.const"() <{"value" = #felt<const 4> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %inner = "felt.mul"(%x, %c3) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %outer = "felt.mul"(%inner, %c4) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  "constrain.eq"(%outer, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
}) : () -> ()

// After folding, a single mul x (const 12) remains; the original two
// constants and the inner mul are dead and get erased.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %[[C12:[^ ]+]] = "felt.const"() <{"value" = #felt<const 12> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-NEXT:     %[[P:[^ ]+]] = "felt.mul"(%{{[^,]+}}, %[[C12]]) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
// CHECK-NEXT:     "constrain.eq"(%[[P]], %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NOT:    #felt<const 3>
// CHECK-NOT:    #felt<const 4>
