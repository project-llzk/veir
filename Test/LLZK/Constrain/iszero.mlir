// RUN: VEIR_ROUNDTRIP

// The circomlib IsZero gadget, translated into the restricted (field-native)
// fragment from llzk-lib's test/Conversions/llzk_to_smt_no_cf_iszero.llzk.
//
// Deltas from the source `@constrain` body, both deliberate:
// - `struct.readm @out` / `@inv` become block arguments (signals) until the
//   Struct dialect lands (M3) — the move anticipated by `Signal`'s docstring
//   in Veir/Dialects/LLZK/Semantics/Constraint.lean.
// - The `bool.cmp ne` + empty `scf.if` pair is dropped: both branches are
//   empty and the result is otherwise unused, so it contributes no
//   constraints — and it is outside the modelled fragment (evalBody would
//   return none on it).
//
// Signals (seedBlockArgs numbering): %in = 0, %out = 1, %inv = 2.
// Constraint system: out = -in*inv + 1  and  in*out = 0.
// At p = 7: (in, out, inv) = (0, 1, k) satisfies for every k, and so does
// (2, 0, 4); (2, 1, 4) does not. `felt.inv` stays behind in `@compute`,
// which the block-level model treats as free.

"builtin.module"() ({
^bb0(%in: !felt.type, %out: !felt.type, %inv: !felt.type):
  %0 = "felt.neg"(%in) : (!felt.type) -> !felt.type
  %1 = "felt.mul"(%0, %inv) : (!felt.type, !felt.type) -> !felt.type
  %c1 = "felt.const"() <{"value" = #felt<const 1> : !felt.type}> : () -> !felt.type
  %2 = "felt.add"(%1, %c1) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%out, %2) : (!felt.type, !felt.type) -> ()
  %3 = "felt.mul"(%in, %out) : (!felt.type, !felt.type) -> !felt.type
  %c0 = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
  "constrain.eq"(%3, %c0) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// Unlike the dedup test, the CHECK lines here pin the def-use wiring, not
// just the op sequence — for IsZero the wiring is the constraint system.
// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}(%[[IN:[0-9a-zA-Z_]+]] : !felt.type, %[[OUT:[0-9a-zA-Z_]+]] : !felt.type, %[[INV:[0-9a-zA-Z_]+]] : !felt.type):
// CHECK-NEXT:      %[[NEG:[0-9a-zA-Z_]+]] = "felt.neg"(%[[IN]])
// CHECK-NEXT:      %[[PROD:[0-9a-zA-Z_]+]] = "felt.mul"(%[[NEG]], %[[INV]])
// CHECK-NEXT:      %[[ONE:[0-9a-zA-Z_]+]] = "felt.const"() <{"value" = #felt<const 1> : !felt.type}>
// CHECK-NEXT:      %[[SUM:[0-9a-zA-Z_]+]] = "felt.add"(%[[PROD]], %[[ONE]])
// CHECK-NEXT:      "constrain.eq"(%[[OUT]], %[[SUM]])
// CHECK-NEXT:      %[[ZPROD:[0-9a-zA-Z_]+]] = "felt.mul"(%[[IN]], %[[OUT]])
// CHECK-NEXT:      %[[ZERO:[0-9a-zA-Z_]+]] = "felt.const"() <{"value" = #felt<const 0> : !felt.type}>
// CHECK-NEXT:      "constrain.eq"(%[[ZPROD]], %[[ZERO]])
// CHECK-NEXT: }) : () -> ()
