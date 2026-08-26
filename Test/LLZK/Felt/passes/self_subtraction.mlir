// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Felt self-subtraction: `felt.sub x x -> felt.const 0`.
// Soundness theorem in Veir/Passes/Felt/Proofs.lean (`self_subtraction_to_zero`).
//
// Tests that the SSA value-equality check fires only when both operands
// flow from the SAME defining value, not from two different ops with
// equal contents.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%x: !felt.type, %y: !felt.type, %anchor: !felt.type):
  // Same value on both sides — folds to felt.const 0.
  %s1 = "felt.sub"(%x, %x) : (!felt.type, !felt.type) -> !felt.type
  // Two distinct block-args, even if semantically equal at runtime —
  // doesn't match (lhs ≠ rhs as ValuePtrs). Op survives.
  %s2 = "felt.sub"(%x, %y) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%s1, %anchor) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%s2, %anchor) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// CHECK:        "builtin.module"() ({
// CHECK:          %[[Z:[^ ]+]] = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:     %[[S2:[^ ]+]] = "felt.sub"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:     "constrain.eq"(%[[Z]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:     "constrain.eq"(%[[S2]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:   }) : () -> ()
