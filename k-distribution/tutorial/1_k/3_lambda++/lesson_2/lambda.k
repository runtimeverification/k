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
  syntax Exp ::= Val
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

// Auxiliary task
  rule <k> _:Val ~> `Rho => .K` ...</k> <env> _ => Rho </env>
    [structural]
endmodule
