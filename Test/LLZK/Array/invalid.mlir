// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: symbolic array dimensions (`@N`) are outside VEIR's
// modeled fragment — only concrete integer dimensions parse.

// CHECK: only concrete integer dimensions are supported
"builtin.module"() ({
  "global.def"() <{constant, sym_name = "t", type = !array.type<@N x !felt.type>}> : () -> ()
}) : () -> ()
