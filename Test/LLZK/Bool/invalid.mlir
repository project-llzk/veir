// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: bool.assert with a result triggers the typed
// "Expected 0 results" arm.

// CHECK: Error verifying input program: bool.assert: Expected 0 result(s)
"builtin.module"() ({
^bb0(%a: i1):
  %0 = "bool.assert"(%a) : (i1) -> i1
}) : () -> ()
