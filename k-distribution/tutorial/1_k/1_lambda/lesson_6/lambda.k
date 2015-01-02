// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "modules/substitution.k"

module LAMBDA
  imports SUBSTITUTION

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
  syntax Variable ::= Id
  syntax KResult ::= Val

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]

  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2

  syntax Exp ::= "if" Exp "then" Exp "else" Exp    [strict(1)]
  rule if true  then E else _ => E
  rule if false then _ else E => E
endmodule
