// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module FUNCONS-SYNTAX
  syntax KItem ::= deref(K)                       [strict]
                 | boundValue(Id)
                 | intDivide(K,K)                 [strict]
                 | intPlus(K,K)                   [strict]
                 | intLeq(K,K)                    [strict]
                 | not(K)                         [strict]
                 | ifTrue(K,K,K)                  [strict(1)]
                 | "skip"
                 | asgn(K,K)                      [strict]
                 | whileTrue(K,K)
                 | seq(K,K)                       [strict(1)]
                 | scope(K,K)
                 | bind(Id,K)                     [strict(2)]
                 | alloc(K)                       [strict]
endmodule

module FUNCONS
  imports FUNCONS-SYNTAX
  configuration <T color="yellow">
                  <k color="green"> $PGM:K </k>
                  <env color="red"> .Map </env>
                  <store color="blue"> .Map </store>
                </T>
  syntax KResult ::= Int | Bool | "skip"
  syntax KItem ::= env(Map)

  rule <k> alloc(I:Int) => L ...</k>
       <store>... . => !L:Int |-> I ...</store>
  rule <k> bind(X,L:Int) => skip ...</k>  <env> Rho => Rho[L/X] </env>
  rule <k> boundValue(X) => L ...</k>  <env>... X |-> L </env>
  rule <k> scope(B,S) => seq(B,S) ~> env(Rho) ...</k> <env> Rho </env>
  rule <k> skip ~> (env(Rho) => .) ...</k> <env> _ => Rho </env>
  rule <k> asgn(L:Int,I:Int) => skip ...</k>  <store>... L |-> (_ => I) ...</store>
  rule seq(skip,S) => S
  rule whileTrue(B,S) => ifTrue(B,seq(S,whileTrue(B,S)),skip)
  rule ifTrue(true,S,_) => S
  rule ifTrue(false,_,S) => S
  rule <k> deref(L:Int) => I ...</k> <store>... L |-> I ...</store>
  rule intPlus(I1:Int, I2:Int) => I1 +Int I2
  rule intLeq(I1:Int, I2:Int) => I1 <=Int I2
  rule not(B:Bool) => notBool(B)
endmodule
