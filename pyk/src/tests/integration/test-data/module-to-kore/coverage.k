// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// Exercises impurity analysis with coverage instrumentation.
// #ctz uses #if...#fi (ite), which is polymorphic. With --coverage, ite gets
// instrumented rules calling #logToFile (impure), but ite must NOT be marked
// impure — Java skips polymorphic function rules in its dependency graph.
module COVERAGE-SYNTAX
  imports INT
  imports K-EQUAL
endmodule

module COVERAGE
  imports COVERAGE-SYNTAX

  syntax Int ::= "#ctz" "(" Int ")" [function]
  rule #ctz(N) => #if N modInt 2 ==Int 1 #then 0 #else 1 +Int #ctz(N >>Int 1) #fi  requires N =/=Int 0
endmodule
