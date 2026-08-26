// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Felt right-identity rewrite: `felt.add x (felt.const 0) -> x`.
// Soundness theorem in Veir/Passes/Felt/Proofs.lean.
//
// Each result is anchored by a `constrain.eq` (0 results, side-effecting)
// so the greedy driver's inline dead-op erasure keeps the chain we are
// asserting on. Values left unanchored are erased by the driver itself.

"builtin.module"() ({
^bb0(%a: !felt.type, %anchor: !felt.type):
  %z = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
  %r = "felt.add"(%a, %z) : (!felt.type, !felt.type) -> !felt.type
  // Sanity: a non-matching add (rhs is not zero) is left untouched.
  %c1 = "felt.const"() <{"value" = #felt<const 1> : !felt.type}> : () -> !felt.type
  %s = "felt.add"(%a, %c1) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%r, %anchor) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%s, %anchor) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// The first felt.add is rewritten away: its constrain now consumes the
// block argument directly, and the dead `felt.const 0` is erased. The
// second add survives because its rhs is `felt.const 1`, not 0.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %[[C1:[^ ]+]] = "felt.const"() <{"value" = #felt<const 1> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:     %[[S:[^ ]+]] = "felt.add"(%{{[^,]+}}, %[[C1]]) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:     "constrain.eq"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:     "constrain.eq"(%[[S]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NOT:    "felt.const"() <{"value" = #felt<const 0>
