// RUN: VEIR_ROUNDTRIP
//
// `function.call` with a nested callee path (`@Sub::@compute`), the
// AttrSizedOperandSegments layout attribute, and the affine-map layout
// pair — the shape the circom-derived LLZK corpus uses.

"builtin.module"() ({
  "struct.def"() <{const_params = [], sym_name = "Sub"}> ({
    "struct.field"() <{sym_name = "x", type = !felt.type}> : () -> ()
    "function.def"() <{function_type = (!felt.type) -> !struct.type<@Sub<[]>>, sym_name = "compute"}> ({
    ^bb0(%arg0: !felt.type):
      %self = "struct.new"() : () -> !struct.type<@Sub<[]>>
      "function.return"(%self) : (!struct.type<@Sub<[]>>) -> ()
    }) {function.allow_witness} : () -> ()
    "function.def"() <{function_type = (!struct.type<@Sub<[]>>, !felt.type) -> (), sym_name = "constrain"}> ({
    ^bb0(%arg0: !struct.type<@Sub<[]>>, %arg1: !felt.type):
      "function.return"() : () -> ()
    }) {function.allow_constraint} : () -> ()
  }) : () -> ()
  "function.def"() <{function_type = (!felt.type) -> (), sym_name = "main"}> ({
  ^bb0(%arg0: !felt.type):
    %s = "function.call"(%arg0) <{callee = @Sub::@compute, mapOpGroupSizes = array<i32>, numDimsPerMap = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!felt.type) -> !struct.type<@Sub<[]>>
    "function.call"(%s, %arg0) <{callee = @Sub::@constrain, mapOpGroupSizes = array<i32>, numDimsPerMap = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!struct.type<@Sub<[]>>, !felt.type) -> ()
    "function.call"(%arg0) <{callee = @free_fn}> : (!felt.type) -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "struct.def"() <{"const_params" = [], "sym_name" = "Sub"}> ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "struct.field"() <{"sym_name" = "x", "type" = !felt.type}> : () -> ()
// CHECK-NEXT: "function.def"() <{"function_type" = (!felt.type) -> !struct.type<@Sub<[]>>, "sym_name" = "compute"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !felt.type):
// CHECK-NEXT: %{{.*}} = "struct.new"() : () -> !struct.type<@Sub<[]>>
// CHECK-NEXT: "function.return"(%{{.*}}) : (!struct.type<@Sub<[]>>) -> ()
// CHECK-NEXT: }) {function.allow_witness} : () -> ()
// CHECK-NEXT: "function.def"() <{"function_type" = (!struct.type<@Sub<[]>>, !felt.type) -> (), "sym_name" = "constrain"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !struct.type<@Sub<[]>>, %{{.*}} : !felt.type):
// CHECK-NEXT: "function.return"() : () -> ()
// CHECK-NEXT: }) {function.allow_constraint} : () -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: "function.def"() <{"function_type" = (!felt.type) -> (), "sym_name" = "main"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !felt.type):
// CHECK-NEXT: %{{.*}} = "function.call"(%{{.*}}) <{"callee" = @Sub::@compute, "mapOpGroupSizes" = array<i32>, "numDimsPerMap" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0>}> : (!felt.type) -> !struct.type<@Sub<[]>>
// CHECK-NEXT: "function.call"(%{{.*}}, %{{.*}}) <{"callee" = @Sub::@constrain, "mapOpGroupSizes" = array<i32>, "numDimsPerMap" = array<i32>, "operandSegmentSizes" = array<i32: 2, 0>}> : (!struct.type<@Sub<[]>>, !felt.type) -> ()
// CHECK-NEXT: "function.call"(%{{.*}}) <{"callee" = @free_fn}> : (!felt.type) -> ()
// CHECK-NEXT: "function.return"() : () -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: }) : () -> ()
