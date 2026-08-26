// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Felt constant-fold: registered-field
// `felt.add (felt.const c1) (felt.const c2) -> felt.const (c1+c2)`.
// Soundness theorem in Veir/Passes/Felt/Proofs.lean (`constant_fold_add`).
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%v: !felt.type<"babybear">, %anchor: !felt.type<"babybear">):
  // Both operands constant: folds to felt.const 42.
  %a = "felt.const"() <{"value" = #felt<const 10> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %b = "felt.const"() <{"value" = #felt<const 32> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %sum = "felt.add"(%a, %b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  // Mixed: a constant + a block-arg value. Constant-fold does NOT match;
  // right-identity pattern also doesn't (rhs is 5, not 0). Op survives.
  %five = "felt.const"() <{"value" = #felt<const 5> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %mixed = "felt.add"(%v, %five) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  "constrain.eq"(%sum, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%mixed, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
}) : () -> ()

// The (10+32) add is replaced by a fresh felt.const 42; the mixed add
// stays. The original 10 and 32 constants are dead and get erased.
//
// CHECK:        "builtin.module"() ({
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 42> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 5> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK:          %{{[^ ]+}} = "felt.add"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
// CHECK:        }) : () -> ()
// CHECK-NOT:    #felt<const 10>
// CHECK-NOT:    #felt<const 32>
