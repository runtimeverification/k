require "k-equal.k"
require "builtins/bool-symbolic.k"

module INT-SYMBOLIC-SYNTAX
  imports INT-SYNTAX-HOOKS
  syntax IntSymbolic ::= "symInt" "(" Int ")" [onlyLabel, klabel(symInt)]
  syntax IntSymbolic ::= "symInt" "("  Id ")" [onlyLabel, klabel(symInt)]
  syntax Int ::= IntSymbolic
endmodule  

module INT-SYMBOLIC
  imports INT-HOOKS
  imports K-EQUAL-HOOKS
  imports INT-SYMBOLIC-SYNTAX
  
  
  // arithmetic
  rule isIntSymbolic(I1:IntSymbolic +Int I2:Int) => true [anywhere]
  rule isIntSymbolic(I1:Int +Int I2:IntSymbolic) => true [anywhere]

  rule isIntSymbolic(I1:IntSymbolic -Int I2:Int) => true [anywhere]
  rule isIntSymbolic(I1:Int -Int I2:IntSymbolic) => true [anywhere]

  rule isIntSymbolic(I1:IntSymbolic *Int I2:Int) => true [anywhere]
  rule isIntSymbolic(I1:Int *Int I2:IntSymbolic) => true [anywhere]

  rule isIntSymbolic(I1:IntSymbolic %Int I2:Int) => true [anywhere]
  rule isIntSymbolic(I1:Int %Int I2:IntSymbolic) => true [anywhere]

  rule isIntSymbolic(I1:IntSymbolic /Int I2:Int) => true when I2 =/=Int 0 [anywhere]
  rule isIntSymbolic(I1:Int /Int I2:IntSymbolic) => true [anywhere]

  rule isIntSymbolic(minInt(I1:IntSymbolic, I2:Int)) => true [anywhere]
  rule isIntSymbolic(minInt(I1:Int, I2:IntSymbolic)) => true [anywhere]

  // relational
  rule isBoolSymbolic(I1:IntSymbolic <=Int I2:Int) => true [anywhere]
  rule isBoolSymbolic(I1:Int  <=Int I2:IntSymbolic) => true [anywhere]

  rule isBoolSymbolic(I1:IntSymbolic  >=Int I2:Int) => true [anywhere]
  rule isBoolSymbolic(I1:Int  >=Int I2:IntSymbolic) => true [anywhere]

  rule isBoolSymbolic(I1:IntSymbolic  <Int I2:Int) => true [anywhere]
  rule isBoolSymbolic(I1:Int  <Int I2:IntSymbolic) => true [anywhere]

  rule isBoolSymbolic(I1:IntSymbolic  >Int I2:Int) => true [anywhere]
  rule isBoolSymbolic(I1:Int  >Int I2:IntSymbolic) => true [anywhere]

  rule isBoolSymbolic(I1:IntSymbolic  ==Int I2:Int) => true [anywhere]
  rule isBoolSymbolic(I1:Int  ==Int I2:IntSymbolic) => true [anywhere]

  rule isBoolSymbolic(I1:IntSymbolic  =/=Int I2:Int) => true [anywhere]
  rule isBoolSymbolic(I1:Int  =/=Int I2:IntSymbolic) => true [anywhere]

  rule isBoolSymbolic(I1:IntSymbolic  dividesInt I2:Int) => true [anywhere]
  rule isBoolSymbolic(I1:Int  dividesInt I2:IntSymbolic) => true [anywhere]

endmodule
