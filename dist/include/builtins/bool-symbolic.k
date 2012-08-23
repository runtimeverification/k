require "k-equal.k"

module BOOL-SYMBOLIC-SYNTAX
  imports BOOL-SYNTAX-HOOKS
  syntax BoolSymbolic ::= "symBool" "(" Int ")"
  syntax BoolSymbolic ::= "symBool" "(" Id ")"
  syntax Bool ::= BoolSymbolic
endmodule

module BOOL-SYMBOLIC
  imports BOOL-HOOKS
  imports K-EQUAL-HOOKS
  imports BOOL-SYMBOLIC-SYNTAX
  
  rule isBoolSymbolic(notBool B:BoolSymbolic) => true [anywhere]

  rule isBoolSymbolic(B1:BoolSymbolic andBool B2:Bool) => true [anywhere]
  rule isBoolSymbolic(B1:Bool andBool B2:BoolSymbolic) => true [anywhere]

  rule isBoolSymbolic(B1:BoolSymbolic andThenBool B2:Bool) => true [anywhere]
  rule isBoolSymbolic(B1:Bool andThenBool B2:BoolSymbolic) => true [anywhere]

  rule isBoolSymbolic(B1:BoolSymbolic xorBool B2:Bool) => true [anywhere]
  rule isBoolSymbolic(B1:Bool xorBool B2:BoolSymbolic) => true [anywhere]

  rule isBoolSymbolic(B1:BoolSymbolic orBool B2:Bool) => true [anywhere]
  rule isBoolSymbolic(B1:Bool orBool B2:BoolSymbolic) => true [anywhere]

  rule isBoolSymbolic(B1:BoolSymbolic orElseBool B2:Bool) => true [anywhere]
  rule isBoolSymbolic(B1:Bool orElseBool B2:BoolSymbolic) => true [anywhere]

  rule isBoolSymbolic(B1:BoolSymbolic impliesBool B2:Bool) => true [anywhere]
  rule isBoolSymbolic(B1:Bool impliesBool B2:BoolSymbolic) => true [anywhere]

  rule isBoolSymbolic(B1:BoolSymbolic ==Bool B2:Bool) => true [anywhere]
  rule isBoolSymbolic(B1:Bool ==Bool B2:BoolSymbolic) => true [anywhere]

  rule isBoolSymbolic(B1:BoolSymbolic =/=Bool B2:Bool) => true [anywhere]
  rule isBoolSymbolic(B1:Bool =/=Bool B2:BoolSymbolic) => true [anywhere]
  
//  rule isBool(B:BoolSymbolic) => true [anywhere]

//@ Some simplification rules.

  rule B:Bool impliesBool true => true  [anywhere]

  rule (B:Bool andBool B':Bool) impliesBool B => true  [anywhere]
  rule (B':Bool andBool B:Bool) impliesBool B => true  [anywhere]

  rule B:Bool andBool true => B  [anywhere]

  rule true andBool B:Bool => B  [anywhere]

  rule B:Bool orBool true => true  [anywhere]

  rule true orBool B:Bool => true  [anywhere]

  rule B:Bool impliesBool B => true [anywhere]

  
endmodule
