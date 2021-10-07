module SMTLEMMACHECK
  imports BOOL
  imports INT
  imports K-EQUAL

  syntax KItem ::= a(Int)
  syntax Int ::= f(Int)  [function, functional]

  rule f(0) => 0
  rule f(_) => 1  [owise]

  rule f(_) >Int -1 andBool false => true  [simplification, smt-lemma]

  rule a(X) => .K requires f(X) >=Int -1

endmodule
