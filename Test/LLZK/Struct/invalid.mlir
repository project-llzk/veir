// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: struct.field with no sym_name must fail in the typed
// properties dispatch, proving the registered path (not the unregistered
// fallthrough) is reached.

// CHECK: missing 'sym_name' property
"builtin.module"() ({
  "struct.def"() <{const_params = [], sym_name = "Bad"}> ({
    "struct.field"() <{type = !felt.type}> : () -> ()
  }) : () -> ()
}) : () -> ()
