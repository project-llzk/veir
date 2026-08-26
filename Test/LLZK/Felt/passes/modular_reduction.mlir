// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Registered-field constant folds reduce through the accepted field registry.
// Bare felt types do not fold because their modulus is unresolved.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%anchor: !felt.type<"babybear">, %raw_anchor: !felt.type):
  %add_a = "felt.const"() <{"value" = #felt<const 2013265920> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %add_b = "felt.const"() <{"value" = #felt<const 2> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %add = "felt.add"(%add_a, %add_b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">

  %neg_in = "felt.const"() <{"value" = #felt<const 5> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %neg = "felt.neg"(%neg_in) : (!felt.type<"babybear">) -> !felt.type<"babybear">

  %raw_a = "felt.const"() <{"value" = #felt<const 2013265920> : !felt.type}> : () -> !felt.type
  %raw_b = "felt.const"() <{"value" = #felt<const 2> : !felt.type}> : () -> !felt.type
  %raw_add = "felt.add"(%raw_a, %raw_b) : (!felt.type, !felt.type) -> !felt.type

  "constrain.eq"(%add, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%neg, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%raw_add, %raw_anchor) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// The two babybear folds reduce modulo the registered prime. The bare-felt
// add does NOT fold, so its operand constants stay live.
//
// CHECK:          "builtin.module"() ({
// CHECK-DAG:        %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 1> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-DAG:        %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 2013265916> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-DAG:        %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 2013265920> : !felt.type}> : () -> !felt.type
// CHECK-DAG:        %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 2> : !felt.type}> : () -> !felt.type
// CHECK:            %{{[^ ]+}} = "felt.add"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NOT:        #felt<const 2013265922> : !felt.type<"babybear">
// CHECK-NOT:        #felt<const 2013265922> : !felt.type
// CHECK-NOT:        #felt<const -5> : !felt.type<"babybear">
// CHECK:          }) : () -> ()
