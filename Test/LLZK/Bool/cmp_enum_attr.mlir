// RUN: veir-opt %s | filecheck %s
//
// bool.cmp with all six FeltCmpPredicate values written in LLZK's own
// `#bool<...>` enum spelling — what `llzk-opt --mlir-print-op-generic`
// emits. Companion to cmp.mlir, which covers the `N : i32` spelling.
//
// The parser normalises the enum form to the integer form, so the two
// tests share their CHECK lines. That normalisation is deliberate and
// not print-faithful: reading `#bool<lt>` prints back `2 : i32`. See
// `parseOptionalBoolCmpPredicateAttr` in Veir/Parser/AttrParser.lean.
// Mapping: eq=0, ne=1, lt=2, le=3, gt=4, ge=5.

"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %eq = "bool.cmp"(%a, %b) <{predicate = #bool<eq>}> : (!felt.type, !felt.type) -> i1
  %ne = "bool.cmp"(%a, %b) <{predicate = #bool<ne>}> : (!felt.type, !felt.type) -> i1
  %lt = "bool.cmp"(%a, %b) <{predicate = #bool<lt>}> : (!felt.type, !felt.type) -> i1
  %le = "bool.cmp"(%a, %b) <{predicate = #bool<le>}> : (!felt.type, !felt.type) -> i1
  %gt = "bool.cmp"(%a, %b) <{predicate = #bool<gt>}> : (!felt.type, !felt.type) -> i1
  %ge = "bool.cmp"(%a, %b) <{predicate = #bool<ge>}> : (!felt.type, !felt.type) -> i1
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}(%{{.*}}: !felt.type, %{{.*}}: !felt.type):
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i32}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = 1 : i32}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i32}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = 3 : i32}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = 4 : i32}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = 5 : i32}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT: }) : () -> ()
