require "lambda.k"

module CALLCC-SYNTAX imports LAMBDA-SYNTAX
  syntax K ::= "callcc" K [strict]
             | "cc" "(" K ")" [latex("{\it cc}({#1})")]
endmodule

module CALLCC 
  imports CALLCC-SYNTAX
  imports LAMBDA
  syntax KResult ::= "cc" "(" K ")" [latex("{\it cc}({#1})")]
  rule [save-cxt] : 
      <k>(callcc(V:KResult) => (V cc(K:K))) ~> K</k> 
  rule [restore-cxt] : 
      <k> (cc(K) V)~> _ => V ~> K</k> 
endmodule
