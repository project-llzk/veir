// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: string.new with 2 results triggers the typed
// "Expected 1 result" arm. The unregistered fallthrough accepts
// any arity, so the message's presence confirms the .string
// String_.new path is reached.

// CHECK: Error verifying input program: string.new: Expected 1 result(s)
"builtin.module"() ({
^bb0():
  %0:2 = "string.new"() <{value = "hello"}> : () -> (!string.type, !string.type)
}) : () -> ()
