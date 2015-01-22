// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "lambda.k"

module CALLCC-SYNTAX imports LAMBDA-SYNTAX
  syntax Exp ::= "callcc" Exp [callCC, strict]
endmodule

module CALLCC
  imports CALLCC-SYNTAX
  imports LAMBDA
  syntax Val ::= "cc" "(" K ")" [latex({\it cc}({#1}))]
  rule [save-cxt] :
      <k>(callcc(V:KResult) => (V cc(K:K))) ~> K</k>
  rule [restore-cxt] :
      <k> (cc(K) V)~> _ => V ~> K</k>
endmodule
