// Copyright (c) 2012-2015 K Team. All Rights Reserved.

require "domains.k"

module LAMBDA-SYNTAX
  imports LAMBDA-COMMON
  imports ID
endmodule

module LAMBDA-COMMON
  imports DOMAINS-COMMON

  syntax Exp ::= Id
               | "lambda" Id "." Exp  [latex(\lambda{#1}.{#2})]
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]

  syntax Exp ::= Val
  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]

  syntax Exp ::= "let" Id "=" Exp "in" Exp

  syntax Exp ::= "letrec" Id Id "=" Exp "in" Exp
               | "mu" Id "." Exp      [latex(\mu{#1}.{#2})]

  syntax Exp ::= "callcc" Exp  [strict]
endmodule

module LAMBDA
  imports LAMBDA-COMMON
  imports DOMAINS

  configuration <T>
                  <k> $PGM:Exp </k>
                  <env> .Map </env>
                  <store> .Map </store>
                </T>

  syntax Val ::= closure(Map,Id,Exp)
  syntax KResult ::= Val

  rule <k> lambda X:Id . E => closure(Rho,X,E) ...</k>
       <env> Rho </env>
    [structural]
  rule <k> closure(Rho,X,E) V:Val => E ~> Rho' ...</k>
       <env> Rho' => Rho[X <- !N] </env>
       <store>... .Map => (!N:Int |-> V) ...</store>
  rule <k> X => V ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> V ...</store>
  rule <k> _:Val ~> `Rho => .K` ...</k> <env> _ => Rho </env>
    [structural]

  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2

  rule if true  then E else _ => E
  rule if false then _ else E => E

  rule let X = E in E':Exp => (lambda X . E') E                         [macro]

  rule letrec F:Id X = E in E' => let F = mu F . lambda X . E in E'     [macro]

  syntax Exp ::= muclosure(Map,Exp)
  rule <k> mu X . E => muclosure(Rho[X <- !N], E) ...</k>
       <env> Rho </env>
       <store>... .Map => (!N:Int |-> muclosure(Rho[X <- !N], E)) ...</store>
    [structural]
  rule <k> muclosure(Rho,E) => E ~> Rho' ...</k>
       <env> Rho' => Rho </env>

  syntax Val ::= cc(Map,K)
  rule <k> `callcc V:Val => V cc(Rho,K)` ~> K </k> <env> Rho </env>
  rule <k> cc(Rho,K) V:Val ~> _ =>  V ~> K </k> <env> _ => Rho </env>
endmodule
