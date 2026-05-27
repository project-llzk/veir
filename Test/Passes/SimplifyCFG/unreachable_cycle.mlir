// RUN: veir-opt %s -p=simplify-cfg | filecheck %s

// ^entry falls through to ^reach.
// ^dead1 and ^dead2 branch to each other but neither has a predecessor
// reachable from ^entry, so both must be removed.

"builtin.module"() ({
  ^module_body():
    "func.func"() ({
      ^entry(%arg : i32):
        "cf.br"(%arg) [^reach] : (i32) -> ()
      ^dead1(%d1 : i32):
        "cf.br"(%d1) [^dead2] : (i32) -> ()
      ^dead2(%d2 : i32):
        "cf.br"(%d2) [^dead1] : (i32) -> ()
      ^reach(%r : i32):
        %c = "arith.constant"() <{"value" = 0 : i1}> : () -> i1
        "cf.cond_br"(%c, %r, %r) [^reach, ^reach] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : i32):
// CHECK-NEXT:         "cf.br"(%{{.*}}) [^[[tgt:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[tgt]](%{{.*}} : i32):
// CHECK-NEXT:         %{{.*}} = "arith.constant"() <{"value" = 0 : i1}> : () -> i1
// CHECK-NEXT:         "cf.cond_br"
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NOT:  ^dead1
// CHECK-NOT:  ^dead2
