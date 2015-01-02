// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "modules/substitution.k"

module LAMBDA
  imports SUBSTITUTION

  syntax Val ::= Id
               | Int | Bool
               | "lambda" Id "." Exp  [binder, lambda]

  syntax KResult ::= Val
  syntax Variable ::= Id


  syntax Exp ::= Val
               | Exp Exp              [left, strict(1), app]
               | "let" Id "=" Exp "in" Exp [binder(1 -> 3), let]
               | "letrec" Id "=" Exp "in" Exp [binder(1 -> 2, 1 -> 3), letrec]
               | Exp "<=" Exp [leq, strict]
               | Exp "+" Exp [plus, strict]
               | "if" Exp "then" Exp "else" Exp [if, strict(1)]
               | "(" Exp ")"          [bracket]

  syntax priorities app > plus > leq > if > lambda let letrec


  rule (lambda X:Id . E2:Exp) E1:Exp => E2[E1 / X]
  rule let X:Id = E1:Exp in E2:Exp => E2[E1 / X]
  rule letrec X:Id = E1:Exp in E2:Exp => E2[letrec X = E1 in E1 / X]
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule if true then E1:Exp else _ => E1
  rule if false then _ else E2:Exp => E2

endmodule
