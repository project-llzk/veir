// RUN: VEIR_ROUNDTRIP
//
// A faithful (arity-trimmed) slice of the SP1 corpus's Add.llzk as
// `llzk-opt --mlir-print-op-generic` emits it: the `veridise.lang`
// module attribute, a `struct.def` with public and private fields, an
// empty `compute`, and a `constrain` mixing `struct.readf`, felt
// arithmetic, and `constrain.eq`.

"builtin.module"() ({
  "struct.def"() <{const_params = [], sym_name = "Add"}> ({
    "struct.field"() <{sym_name = "add_operation_29", type = !felt.type}> {llzk.pub} : () -> ()
    "struct.field"() <{sym_name = "is_real_33", type = !felt.type}> : () -> ()
    "function.def"() <{function_type = (!felt.type, !felt.type) -> !struct.type<@Add<[]>>, sym_name = "compute"}> ({
    ^bb0(%arg0: !felt.type, %arg1: !felt.type):
      %0 = "struct.new"() : () -> !struct.type<@Add<[]>>
      "function.return"(%0) : (!struct.type<@Add<[]>>) -> ()
    }) {function.allow_witness} : () -> ()
    "function.def"() <{function_type = (!struct.type<@Add<[]>>, !felt.type, !felt.type) -> (), sym_name = "constrain"}> ({
    ^bb0(%arg0: !struct.type<@Add<[]>>, %arg1: !felt.type, %arg2: !felt.type):
      %0 = "felt.const"() <{value = #felt<const 2130673921> : !felt.type}> : () -> !felt.type
      %1 = "struct.readf"(%arg0) <{field_name = @add_operation_29, mapOpGroupSizes = array<i32>, numDimsPerMap = array<i32>}> : (!struct.type<@Add<[]>>) -> !felt.type
      %2 = "felt.add"(%arg1, %arg2) : (!felt.type, !felt.type) -> !felt.type
      %3 = "felt.sub"(%2, %1) : (!felt.type, !felt.type) -> !felt.type
      %4 = "felt.mul"(%3, %0) : (!felt.type, !felt.type) -> !felt.type
      "constrain.eq"(%4, %1) : (!felt.type, !felt.type) -> ()
      "function.return"() : () -> ()
    }) {function.allow_constraint} : () -> ()
  }) : () -> ()
}) {veridise.lang = "llzk"} : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "struct.def"() <{"const_params" = [], "sym_name" = "Add"}> ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "struct.field"() <{"sym_name" = "add_operation_29", "type" = !felt.type}> {llzk.pub} : () -> ()
// CHECK-NEXT: "struct.field"() <{"sym_name" = "is_real_33", "type" = !felt.type}> : () -> ()
// CHECK-NEXT: "function.def"() <{"function_type" = (!felt.type, !felt.type) -> !struct.type<@Add<[]>>, "sym_name" = "compute"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !felt.type, %{{.*}} : !felt.type):
// CHECK-NEXT: %{{.*}} = "struct.new"() : () -> !struct.type<@Add<[]>>
// CHECK-NEXT: "function.return"(%{{.*}}) : (!struct.type<@Add<[]>>) -> ()
// CHECK-NEXT: }) {function.allow_witness} : () -> ()
// CHECK-NEXT: "function.def"() <{"function_type" = (!struct.type<@Add<[]>>, !felt.type, !felt.type) -> (), "sym_name" = "constrain"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !struct.type<@Add<[]>>, %{{.*}} : !felt.type, %{{.*}} : !felt.type):
// CHECK-NEXT: %{{.*}} = "felt.const"() <{"value" = #felt<const 2130673921> : !felt.type}> : () -> !felt.type
// CHECK-NEXT: %{{.*}} = "struct.readf"(%{{.*}}) <{"field_name" = @add_operation_29, "mapOpGroupSizes" = array<i32>, "numDimsPerMap" = array<i32>}> : (!struct.type<@Add<[]>>) -> !felt.type
// CHECK-NEXT: %{{.*}} = "felt.add"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT: %{{.*}} = "felt.sub"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT: %{{.*}} = "felt.mul"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT: "constrain.eq"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT: "function.return"() : () -> ()
// CHECK-NEXT: }) {function.allow_constraint} : () -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: }) {"veridise.lang" = "llzk"} : () -> ()
