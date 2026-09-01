// RUN: VEIR_ROUNDTRIP
//
// Round-trips both struct-dialect generations:
// - the older mnemonics (`struct.field`/`struct.readf`/`struct.writef`,
//   `field_name` key, `const_params` on `struct.def`) that
//   `llzk-opt --mlir-print-op-generic` emits for the SP1 corpus, and
// - the current mnemonics (`struct.member`/`struct.readm`/`struct.writem`,
//   `member_name` key, no `const_params`).
// `{llzk.pub}` is a discardable attribute and must survive the round-trip.

"builtin.module"() ({
  "struct.def"() <{const_params = [], sym_name = "Add"}> ({
    "struct.field"() <{sym_name = "x", type = !felt.type}> {llzk.pub} : () -> ()
    "struct.field"() <{sym_name = "y", type = !felt.type}> : () -> ()
    "function.def"() <{function_type = (!felt.type) -> !struct.type<@Add<[]>>, sym_name = "compute"}> ({
    ^bb0(%arg0: !felt.type):
      %self = "struct.new"() : () -> !struct.type<@Add<[]>>
      "struct.writef"(%self, %arg0) <{field_name = @x}> : (!struct.type<@Add<[]>>, !felt.type) -> ()
      "function.return"(%self) : (!struct.type<@Add<[]>>) -> ()
    }) {function.allow_witness} : () -> ()
    "function.def"() <{function_type = (!struct.type<@Add<[]>>, !felt.type) -> (), sym_name = "constrain"}> ({
    ^bb0(%arg0: !struct.type<@Add<[]>>, %arg1: !felt.type):
      %0 = "struct.readf"(%arg0) <{field_name = @x, mapOpGroupSizes = array<i32>, numDimsPerMap = array<i32>}> : (!struct.type<@Add<[]>>) -> !felt.type
      "constrain.eq"(%0, %arg1) : (!felt.type, !felt.type) -> ()
      "function.return"() : () -> ()
    }) {function.allow_constraint} : () -> ()
  }) : () -> ()
  "struct.def"() <{sym_name = "New"}> ({
    "struct.member"() <{signal, sym_name = "m", type = !felt.type}> : () -> ()
    "struct.member"() <{column, sym_name = "c", type = !felt.type}> : () -> ()
    "function.def"() <{function_type = (!struct.type<@New>, !felt.type) -> (), sym_name = "constrain"}> ({
    ^bb0(%arg0: !struct.type<@New>, %arg1: !felt.type):
      %0 = "struct.readm"(%arg0) <{mapOpGroupSizes = array<i32>, member_name = @m, numDimsPerMap = array<i32>}> : (!struct.type<@New>) -> !felt.type
      "struct.writem"(%arg0, %arg1) <{member_name = @m}> : (!struct.type<@New>, !felt.type) -> ()
      "constrain.eq"(%0, %arg1) : (!felt.type, !felt.type) -> ()
      "function.return"() : () -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "struct.def"() <{"const_params" = [], "sym_name" = "Add"}> ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "struct.field"() <{"sym_name" = "x", "type" = !felt.type}> {llzk.pub} : () -> ()
// CHECK-NEXT: "struct.field"() <{"sym_name" = "y", "type" = !felt.type}> : () -> ()
// CHECK-NEXT: "function.def"() <{"function_type" = (!felt.type) -> !struct.type<@Add<[]>>, "sym_name" = "compute"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !felt.type):
// CHECK-NEXT: %{{.*}} = "struct.new"() : () -> !struct.type<@Add<[]>>
// CHECK-NEXT: "struct.writef"(%{{.*}}, %{{.*}}) <{"field_name" = @x}> : (!struct.type<@Add<[]>>, !felt.type) -> ()
// CHECK-NEXT: "function.return"(%{{.*}}) : (!struct.type<@Add<[]>>) -> ()
// CHECK-NEXT: }) {function.allow_witness} : () -> ()
// CHECK-NEXT: "function.def"() <{"function_type" = (!struct.type<@Add<[]>>, !felt.type) -> (), "sym_name" = "constrain"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !struct.type<@Add<[]>>, %{{.*}} : !felt.type):
// CHECK-NEXT: %{{.*}} = "struct.readf"(%{{.*}}) <{"field_name" = @x, "mapOpGroupSizes" = array<i32>, "numDimsPerMap" = array<i32>}> : (!struct.type<@Add<[]>>) -> !felt.type
// CHECK-NEXT: "constrain.eq"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT: "function.return"() : () -> ()
// CHECK-NEXT: }) {function.allow_constraint} : () -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: "struct.def"() <{"sym_name" = "New"}> ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "struct.member"() <{signal, "sym_name" = "m", "type" = !felt.type}> : () -> ()
// CHECK-NEXT: "struct.member"() <{column, "sym_name" = "c", "type" = !felt.type}> : () -> ()
// CHECK-NEXT: "function.def"() <{"function_type" = (!struct.type<@New>, !felt.type) -> (), "sym_name" = "constrain"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !struct.type<@New>, %{{.*}} : !felt.type):
// CHECK-NEXT: %{{.*}} = "struct.readm"(%{{.*}}) <{"mapOpGroupSizes" = array<i32>, "member_name" = @m, "numDimsPerMap" = array<i32>}> : (!struct.type<@New>) -> !felt.type
// CHECK-NEXT: "struct.writem"(%{{.*}}, %{{.*}}) <{"member_name" = @m}> : (!struct.type<@New>, !felt.type) -> ()
// CHECK-NEXT: "constrain.eq"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT: "function.return"() : () -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: }) : () -> ()
