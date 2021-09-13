// Copyright (c) 2012-2019 K Team. All Rights Reserved.

require "substitution.md"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX

  syntax Val ::= KVar
               | "lambda" KVar "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]

  syntax Val ::= Int | Bool
  syntax Exp ::= "-" Int
               > Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]

  syntax Exp ::= "let" KVar "=" Exp "in" Exp
  rule let X = E in E':Exp => (lambda X . E') E                        [macro]

  syntax Exp ::= "letrec" KVar KVar "=" Exp "in" Exp
               | "mu" KVar "." Exp                 [binder, latex(\mu{#1}.{#2})]
  rule letrec F:KVar X = E in E' => let F = mu F . lambda X . E in E'    [macro]

  syntax Exp ::= "callcc" Exp  [strict]
  syntax Val ::= cc(K)
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS

  syntax KResult ::= Val

  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]

  rule - I => 0 -Int I
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2

  rule if true  then E else _ => E
  rule if false then _ else E => E

  rule mu X . E => E[(mu X . E) / X]

  rule <k> (callcc V:Val => V cc(K)) ~> K </k>
  rule <k> cc(K) V ~> _ =>  V ~> K </k>
endmodule
