// RUN: veir-opt %s | filecheck %s
//
// bool.cmp with all six FeltCmpPredicate values written in LLZK's own
// `#bool<...>` enum spelling — what `llzk-opt --mlir-print-op-generic`
// emits — plus the older generation's `#bool<cmp lt>` spelling used by
// the SP1 corpus. Companion to cmp.mlir, which covers the `N : i32`
// spelling.
//
// Each spelling round-trips *faithfully*: the enum forms print back as
// enum forms (llzk-opt only accepts those back into `bool.cmp`'s
// properties, so re-ingestion by LLZK tooling depends on it) and the
// integer form prints back as an integer. See
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
  %oldlt = "bool.cmp"(%a, %b) <{predicate = #bool<cmp lt>}> : (!felt.type, !felt.type) -> i1
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}(%{{.*}}: !felt.type, %{{.*}}: !felt.type):
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<eq>}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<ne>}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<lt>}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<le>}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<gt>}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<ge>}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<cmp lt>}> : (!felt.type, !felt.type) -> i1
// CHECK-NEXT: }) : () -> ()
