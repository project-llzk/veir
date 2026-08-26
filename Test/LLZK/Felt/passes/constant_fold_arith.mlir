// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Constant-fold registered-field sub, mul, neg.
// Soundness: constant_fold_sub, constant_fold_mul, constant_fold_neg.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%anchor: !felt.type<"babybear">):
  %a = "felt.const"() <{"value" = #felt<const 7> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %b = "felt.const"() <{"value" = #felt<const 3> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %d = "felt.sub"(%a, %b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %p = "felt.mul"(%a, %b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %n = "felt.neg"(%a) : (!felt.type<"babybear">) -> !felt.type<"babybear">
  "constrain.eq"(%d, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%p, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%n, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
}) : () -> ()

// Each arithmetic op folds to its computed value; the operand constants
// are dead afterwards and get erased.
//
// CHECK:        "builtin.module"() ({
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 4> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 21> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 2013265914> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-NOT:      "felt.sub"
// CHECK-NOT:      "felt.mul"
// CHECK-NOT:      "felt.neg"
// CHECK:        }) : () -> ()
