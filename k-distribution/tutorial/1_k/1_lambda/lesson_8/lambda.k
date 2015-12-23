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
  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]
               | "let" Id "=" Exp "in" Exp
               | "letrec" Id Id "=" Exp "in" Exp
               | "mu" Id "." Exp      [binder, latex(\mu{#1}.{#2})]
  syntax KVariable ::= Id
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS
  imports SUBSTITUTION

  syntax KResult ::= Val

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]

  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2

  rule if true  then E else _ => E
  rule if false then _ else E => E

  rule let X = E in E':Exp => (lambda X . E') E                         [macro]
  rule letrec F:Id X = E in E' => let F = mu F . lambda X . E in E'     [macro]
  rule mu X . E => E[(mu X . E) / X]
endmodule
