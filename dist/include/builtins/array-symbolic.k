
module ARRAY-SYMBOLIC-SYNTAX
  imports INT-SYNTAX-HOOKS
  syntax ArraySymbolic ::= "symArray" "(" Int ")" [onlyLabel, klabel(symArray)]
  syntax ArraySymbolic ::= "symArray" "("  Id ")" [onlyLabel, klabel(symArray)]
  syntax Array ::= ArraySymbolic
endmodule  

module ARRAY-SYMBOLIC
  imports ARRAY-SYMBOLIC-SYNTAX

  syntax Int ::= "select" Array Int
  syntax Array ::= "store" Array K Int

  rule isIntSymbolic(select A:Array I:Int) => isArraySymbolic(A) [anywhere]
  rule isArraySymbolic(store A:Array P:Int I:Int) => isArraySymbolic(A) [anywhere]
  rule isArraySymbolic(symArray(I:Int)) => true [anywhere]
  rule isArraySymbolic(symArray(X:Id))  => true [anywhere]
endmodule
