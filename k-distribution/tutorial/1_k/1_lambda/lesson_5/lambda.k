// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "domains.k"
require "substitution.k"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
  syntax KVariable ::= Id
  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS
  imports SUBSTITUTION
  syntax KResult ::= Val

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]

  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2
//  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2
endmodule
