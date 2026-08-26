// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Felt associativity canonicalization:
//   felt.add (felt.add x c1) c2  ->  felt.add x (c1+c2)
// Soundness theorem in Veir/Passes/Felt/Proofs.lean (`assoc_const_fold_add`).
//
// Combined with constant_fold_add, this lets the pass fully fold long
// sums of constants into a single rewrite. Demonstrates a pattern that
// walks the defining op chain (matchAddFromValue + matchConstFromValue)
// without needing dominance reasoning beyond what definingOp? gives.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%x: !felt.type<"babybear">, %anchor: !felt.type<"babybear">):
  // ((x + 10) + 32) ->[assoc] (x + 42)
  %c10 = "felt.const"() <{"value" = #felt<const 10> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %inner = "felt.add"(%x, %c10) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %c32 = "felt.const"() <{"value" = #felt<const 32> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %outer = "felt.add"(%inner, %c32) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  "constrain.eq"(%outer, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
}) : () -> ()

// After felt-combine: a single `felt.add %x (felt.const 42)`. The inner
// add and the two original constants are dead and get erased.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %[[C42:[^ ]+]] = "felt.const"() <{"value" = #felt<const 42> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-NEXT:     %[[SUM:[^ ]+]] = "felt.add"(%{{[^,]+}}, %[[C42]]) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
// CHECK-NEXT:     "constrain.eq"(%[[SUM]], %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NOT:    #felt<const 10>
// CHECK-NOT:    #felt<const 32>
