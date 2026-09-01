// RUN: VEIR_ROUNDTRIP
//
// Round-trips the array dialect and `!array.type`, including the lookup
// idiom real circuits use: `global.read` a table, `array.new` a tuple,
// `constrain.in` the containment.

"builtin.module"() ({
  "global.def"() <{constant, sym_name = "byte_xor", type = !array.type<65536,3 x !felt.type>}> : () -> ()
  "function.def"() <{function_type = (!felt.type, !felt.type, !felt.type) -> (), sym_name = "constrain"}> ({
  ^bb0(%arg0: !felt.type, %arg1: !felt.type, %arg2: !felt.type):
    %arr = "array.new"(%arg0, %arg1, %arg2) <{mapOpGroupSizes = array<i32>, numDimsPerMap = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!felt.type, !felt.type, !felt.type) -> !array.type<3 x !felt.type>
    %tbl = "global.read"() <{name_ref = @byte_xor}> : () -> !array.type<65536,3 x !felt.type>
    "constrain.in"(%tbl, %arr) : (!array.type<65536,3 x !felt.type>, !array.type<3 x !felt.type>) -> ()
    "function.return"() : () -> ()
  }) {function.allow_constraint} : () -> ()
  "function.def"() <{function_type = (!array.type<2,2 x !felt.type>, index, index, !felt.type) -> (), sym_name = "rw"}> ({
  ^bb0(%arg0: !array.type<2,2 x !felt.type>, %arg1: index, %arg2: index, %arg3: !felt.type):
    %0 = "array.read"(%arg0, %arg1, %arg2) : (!array.type<2,2 x !felt.type>, index, index) -> !felt.type
    "array.write"(%arg0, %arg1, %arg2, %arg3) : (!array.type<2,2 x !felt.type>, index, index, !felt.type) -> ()
    %1 = "array.extract"(%arg0, %arg1) : (!array.type<2,2 x !felt.type>, index) -> !array.type<2 x !felt.type>
    "array.insert"(%arg0, %arg1, %1) : (!array.type<2,2 x !felt.type>, index, !array.type<2 x !felt.type>) -> ()
    %2 = "array.len"(%arg0, %arg1) : (!array.type<2,2 x !felt.type>, index) -> index
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "global.def"() <{constant, "sym_name" = "byte_xor", "type" = !array.type<65536,3 x !felt.type>}> : () -> ()
// CHECK-NEXT: "function.def"() <{"function_type" = (!felt.type, !felt.type, !felt.type) -> (), "sym_name" = "constrain"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !felt.type, %{{.*}} : !felt.type, %{{.*}} : !felt.type):
// CHECK-NEXT: %{{.*}} = "array.new"(%{{.*}}, %{{.*}}, %{{.*}}) <{"mapOpGroupSizes" = array<i32>, "numDimsPerMap" = array<i32>, "operandSegmentSizes" = array<i32: 3, 0>}> : (!felt.type, !felt.type, !felt.type) -> !array.type<3 x !felt.type>
// CHECK-NEXT: %{{.*}} = "global.read"() <{"name_ref" = @byte_xor}> : () -> !array.type<65536,3 x !felt.type>
// CHECK-NEXT: "constrain.in"(%{{.*}}, %{{.*}}) : (!array.type<65536,3 x !felt.type>, !array.type<3 x !felt.type>) -> ()
// CHECK-NEXT: "function.return"() : () -> ()
// CHECK-NEXT: }) {function.allow_constraint} : () -> ()
// CHECK-NEXT: "function.def"() <{"function_type" = (!array.type<2,2 x !felt.type>, index, index, !felt.type) -> (), "sym_name" = "rw"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !array.type<2,2 x !felt.type>, %{{.*}} : index, %{{.*}} : index, %{{.*}} : !felt.type):
// CHECK-NEXT: %{{.*}} = "array.read"(%{{.*}}, %{{.*}}, %{{.*}}) : (!array.type<2,2 x !felt.type>, index, index) -> !felt.type
// CHECK-NEXT: "array.write"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) : (!array.type<2,2 x !felt.type>, index, index, !felt.type) -> ()
// CHECK-NEXT: %{{.*}} = "array.extract"(%{{.*}}, %{{.*}}) : (!array.type<2,2 x !felt.type>, index) -> !array.type<2 x !felt.type>
// CHECK-NEXT: "array.insert"(%{{.*}}, %{{.*}}, %{{.*}}) : (!array.type<2,2 x !felt.type>, index, !array.type<2 x !felt.type>) -> ()
// CHECK-NEXT: %{{.*}} = "array.len"(%{{.*}}, %{{.*}}) : (!array.type<2,2 x !felt.type>, index) -> index
// CHECK-NEXT: "function.return"() : () -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: }) : () -> ()
