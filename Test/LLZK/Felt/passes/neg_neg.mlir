// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.neg (felt.neg x) -> x.  Soundness: neg_neg_to_self.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%a: !felt.type, %anchor: !felt.type):
  %n1 = "felt.neg"(%a) : (!felt.type) -> !felt.type
  %n2 = "felt.neg"(%n1) : (!felt.type) -> !felt.type
  "constrain.eq"(%n2, %anchor) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// The outer neg is replaced by the block argument, leaving the inner neg
// dead; the driver erases it, so no felt.neg survives at all.
//
// CHECK:        "builtin.module"() ({
// CHECK-NEXT:     ^{{.*}}:
// CHECK-NEXT:     "constrain.eq"({{.*}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:   }) : () -> ()
