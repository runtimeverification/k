// Copyright (c) 2012-2014 K Team. All Rights Reserved.
module LAMBDA
  syntax Exp ::= Id
               | "lambda" Id "." Exp  [latex(\lambda{#1}.{#2})]
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]

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
  rule <k> _:Val ~> (Rho => .) ...</k> <env> _ => Rho </env>
    [structural]

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

  syntax Exp ::= "let" Id "=" Exp "in" Exp
  rule let X = E in E':Exp => (lambda X . E') E                         [macro]

  syntax Exp ::= "letrec" Id Id "=" Exp "in" Exp
               | "mu" Id "." Exp      [latex(\mu{#1}.{#2})]
  rule letrec F:Id X = E in E' => let F = mu F . lambda X . E in E'     [macro]

  syntax Exp ::= muclosure(Map,Exp)
  rule <k> mu X . E => muclosure(Rho[X <- !N], E) ...</k>
       <env> Rho </env>
       <store>... .Map => (!N:Int |-> muclosure(Rho[X <- !N], E)) ...</store>
    [structural]
  rule <k> muclosure(Rho,E) => E ~> Rho' ...</k>
       <env> Rho' => Rho </env>

  syntax Exp ::= "callcc" Exp  [strict]
  syntax Val ::= cc(Map,K)
  rule <k> (callcc V:Val => V cc(Rho,K)) ~> K </k> <env> Rho </env>
  rule <k> cc(Rho,K) V ~> _ =>  V ~> K </k> <env> _ => Rho </env>
endmodule
