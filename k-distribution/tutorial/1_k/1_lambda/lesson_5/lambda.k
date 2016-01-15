// Copyright (c) 2012-2016 K Team. All Rights Reserved.

require "substitution.k"

module LAMBDA
  imports SUBSTITUTION

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
  syntax KVariable ::= Id
  syntax KResult ::= Val

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]

  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
//  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2
endmodule
