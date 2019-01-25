// Copyright (c) 2012-2019 K Team. All Rights Reserved.

require "domains.k"
require "common.k"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Val ::= Int | Bool
  syntax Exp ::= Val
               | Id
               | "lambda" Id "." Exp  [latex(\lambda{#1}.{#2})]
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
               | Exp "*" Exp          [strict, left, klabel(mull)]
               | Exp "/" Exp          [strict, klabel(divl)]
               > Exp "+" Exp          [seqstrict, left, klabel(addl)]
               > Exp "<=" Exp         [strict, klabel(lel)]
  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)] // Conditional
               | "let" Id "=" Exp "in" Exp                   // Let binder
               | "letrec" Id Id "=" Exp "in" Exp             // Letrec
               | "mu" Id "." Exp      [latex(\mu{#1}.{#2})]  // Mu

endmodule

module LAMBDA
  imports DOMAINS
  imports LAMBDA-SYNTAX
  imports COMMON

  configuration <L2 color="yellow">
                  <k color="green"> $PGM:Exp </k>
                  <env color="blue"> .Map </env>
                  <store color="red"> .Map </store>
                </L2>

  syntax KResult ::= Val

  syntax Val ::= closure(Map,Id,Exp)
    [latex(\textsf{closure}_\lambda({#1},{#2},{#3}))]

  rule <k> lambda X:Id . E => closure(Rho,X,E) ...</k>
       <env> Rho </env>
    [structural]
  rule <k> closure(Rho,X,E) V:Val => E ~> Rho' ...</k>
       <env> Rho' => Rho[X <- !N] </env>
       <store>... .Map => (!N:Int |-> V) ...</store>
  rule <k> X:Id => V ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> V ...</store>

  rule <k> _:Val ~> (Rho:Map => .) ...</k> <env> _ => Rho </env>
    [structural]

  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2

  rule if true  then E else _ => E
  rule if false then _ else E => E

  rule let X = E in E':Exp => (lambda X . E') E                         [macro]

  rule letrec F:Id X = E in E' => let F = mu F . lambda X . E in E'     [macro]

  syntax Exp ::= muclosure(Map,Exp)
    [latex(\textsf{closure}_\mu({#1},{#2}))]
  rule <k> mu X . E => muclosure(Rho[X <- !N], E) ...</k>
       <env> Rho </env>
       <store>... .Map => (!N:Int |-> muclosure(Rho[X <- !N], E)) ...</store>
    [structural]
  rule <k> muclosure(Rho,E) => E ~> Rho' ...</k>
       <env> Rho' => Rho </env>

endmodule
