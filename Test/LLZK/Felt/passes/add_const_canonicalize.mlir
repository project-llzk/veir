// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.add (felt.const c) x  ->  felt.add x (felt.const c)  (canonicalize)
// Followed by right_identity_zero_add firing.
// Soundness: add_const_swap, then right_identity_zero_add.
//
// Results are anchored by `constrain.eq` (0 results, side-effecting) so the
// greedy driver's inline dead-op erasure keeps the chain under test;
// anything left unanchored is erased by the driver itself.

"builtin.module"() ({
^bb0(%a: !felt.type, %anchor: !felt.type):
  %z = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
  // Constant on the LEFT. Without canonicalization,
  // right_identity_zero_add (which matches `add x const`) wouldn't fire.
  %r = "felt.add"(%z, %a) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%r, %anchor) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// After canonicalization the add becomes (a, z); then
// right_identity_zero_add removes it, so the constrain consumes the block
// argument directly and the now-dead `felt.const 0` is erased.
//
// CHECK:        "builtin.module"() ({
// CHECK-NEXT:     ^{{.*}}:
// CHECK-NEXT:     "constrain.eq"({{.*}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:   }) : () -> ()
