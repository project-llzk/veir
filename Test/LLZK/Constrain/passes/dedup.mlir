// RUN: veir-opt -p=llzk-dedup-constraints %s | filecheck %s
//
// Duplicate `constrain.eq` assertions collapse to one; distinct ones survive.
// Note %2 = a*b + 3 is asserted equal to %a twice, and once against %b.

"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %0 = "felt.mul"(%a, %b) : (!felt.type, !felt.type) -> !felt.type
  %1 = "felt.const"() <{"value" = #felt<const 3> : !felt.type}> : () -> !felt.type
  %2 = "felt.add"(%0, %1) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%2, %a) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%2, %a) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%2, %b) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%2, %a) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}(%{{.*}}: !felt.type, %{{.*}}: !felt.type):
// CHECK-NEXT:      %{{.*}} = "felt.mul"
// CHECK-NEXT:      %{{.*}} = "felt.const"
// CHECK-NEXT:      %{{.*}} = "felt.add"
// CHECK-NEXT:      "constrain.eq"
// CHECK-NEXT:      "constrain.eq"
// CHECK-NEXT: }) : () -> ()
