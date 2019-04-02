// Copyright (c) 2012-2019 K Team. All Rights Reserved.

require "substitution.k"

module LAMBDA
  imports DOMAINS
  imports SUBSTITUTION

  syntax Val ::= KVar
               | "lambda" KVar "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
  syntax KResult ::= Val

  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]

  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]
  rule if true  then E else _ => E
  rule if false then _ else E => E

  syntax Exp ::= "let" KVar "=" Exp "in" Exp
  rule let X = E in E':Exp => (lambda X . E') E                        [macro]

  syntax Exp ::= "letrec" KVar KVar "=" Exp "in" Exp
               | "mu" KVar "." Exp      [binder, latex(\mu{#1}.{#2})]
  rule letrec F:KVar X = E in E' => let F = mu F . lambda X . E in E'    [macro]
  rule mu X . E => E[(mu X . E) / X]
endmodule
