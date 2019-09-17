// Copyright (c) 2012-2019 K Team. All Rights Reserved.

require "domains.k"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Val ::= Int | Bool
  syntax Exp ::= Val
               | Id
               | "lambda" Id "." Exp
               | Exp Exp              [left, klabel(appl)]
               | "(" Exp ")"          [bracket]
               | Exp "*" Exp          [left, klabel(mull)]
               | Exp "/" Exp          [klabel(divl)]
               > Exp "+" Exp          [left, klabel(addl)]
               > Exp "<=" Exp         [klabel(lel)]
  syntax Exp ::= "if" Exp "then" Exp "else" Exp   // Conditional
               | "let" Id "=" Exp "in" Exp        // Let binder
               | "letrec" Id Id "=" Exp "in" Exp  // Letrec
               | "mu" Id "." Exp                  // Mu
endmodule

module LAMBDA-CONFIG
  imports DOMAINS
  imports LAMBDA-SYNTAX

  configuration <lambdaT>
    <lambdak> .K /* $PGM:Exp */ </lambdak>
    <lambdaenv> .Map </lambdaenv>
    <lambdastore> .Map </lambdastore>
    <lambdacounter> 1 </lambdacounter>
  </lambdaT>

  syntax KResult ::= Val
endmodule

// TODO: auto-generate
module LAMBDA-STRICT
  imports LAMBDA-CONFIG

  syntax KItem ::= #appl1(K) | #appl2(K)
  rule <lambdak> HOLE E2:Exp => HOLE ~> #appl2(E2) ... </lambdak>   [tag(b), heat]
  rule <lambdak> HOLE ~> #appl2(E2) => HOLE E2:Exp ... </lambdak>   [tag(b), cool]
  rule <lambdak> V1:Val HOLE => HOLE ~> #appl1(V1) ... </lambdak>   [tag(b), heat]
  rule <lambdak> HOLE ~> #appl1(V1) => V1:Val HOLE ... </lambdak>   [tag(b), cool]

  syntax KItem ::= #mull1(K) | #mull2(K)
  rule <lambdak> HOLE * E2 => HOLE ~> #mull2(E2) ... </lambdak>     [tag(b), heat]
  rule <lambdak> HOLE ~> #mull2(E2) => HOLE * E2 ... </lambdak>     [tag(b), cool]
  rule <lambdak> I1:Int * HOLE => HOLE ~> #mull1(I1) ... </lambdak> [tag(b), heat]
  rule <lambdak> HOLE ~> #mull1(I1) => I1 * HOLE ... </lambdak>     [tag(b), cool]

  syntax KItem ::= #divl1(K) | #divl2(K)
  rule <lambdak> HOLE / E2 => HOLE ~> #divl2(E2) ... </lambdak>     [tag(b), heat]
  rule <lambdak> HOLE ~> #divl2(E2) => HOLE / E2 ... </lambdak>     [tag(b), cool]
  rule <lambdak> I1:Int / HOLE => HOLE ~> #divl1(I1) ... </lambdak> [tag(b), heat]
  rule <lambdak> HOLE ~> #divl1(I1) => I1 / HOLE ... </lambdak>     [tag(b), cool]

  syntax KItem ::= #addl1(K) | #addl2(K)
  rule <lambdak> HOLE + E2 => HOLE ~> #addl2(E2) ... </lambdak>     [tag(b), heat]
  rule <lambdak> HOLE ~> #addl2(E2) => HOLE + E2 ... </lambdak>     [tag(b), cool]
  rule <lambdak> I1:Int + HOLE => HOLE ~> #addl1(I1) ... </lambdak> [tag(b), heat]
  rule <lambdak> HOLE ~> #addl1(I1) => I1 + HOLE ... </lambdak>     [tag(b), cool]

  syntax KItem ::= #lel1(K) | #lel2(K)
  rule <lambdak> HOLE <= E2 => HOLE ~> #lel2(E2) ... </lambdak>     [tag(b), heat]
  rule <lambdak> HOLE ~> #lel2(E2) => HOLE <= E2 ... </lambdak>     [tag(b), cool]
  rule <lambdak> I1:Int <= HOLE => HOLE ~> #lel1(I1) ... </lambdak> [tag(b), heat]
  rule <lambdak> HOLE ~> #lel1(I1) => I1 <= HOLE ... </lambdak>     [tag(b), cool]

  syntax KItem ::= #ifl(K,K)
  rule <lambdak> if HOLE then E1 else E2 => HOLE ~> #ifl(E1,E2) ... </lambdak> [tag(b), heat]
  rule <lambdak> HOLE ~> #ifl(E1,E2) => if HOLE then E1 else E2 ... </lambdak> [tag(b), cool]
endmodule

module LAMBDA
  imports DOMAINS
  imports LAMBDA-CONFIG
  imports LAMBDA-STRICT

  syntax Val ::= closure(Map,Id,Exp)

  rule <lambdak> lambda X:Id . E => closure(Rho,X,E) ...</lambdak>
       <lambdaenv> Rho </lambdaenv>
       [tag(b), structural]
  rule <lambdak> closure(Rho,X,E) V:Val => E ~> Rho' ...</lambdak>
       <lambdaenv> Rho' => Rho[X <- N] </lambdaenv>
       <lambdastore>... .Map => (N:Int |-> V) ...</lambdastore>
       <lambdacounter> N => N +Int 1 </lambdacounter>
       [tag(b)]
  rule <lambdak> X:Id => V ...</lambdak>
       <lambdaenv>... X |-> N ...</lambdaenv>
       <lambdastore>... N |-> V ...</lambdastore>
       [tag(b)]

  rule <lambdak> _:Val ~> (Rho:Map => .) ...</lambdak> <lambdaenv> _ => Rho </lambdaenv> [tag(b), structural]

  rule <lambdak> I1:Int * I2:Int => I1 *Int I2   ... </lambdak> [tag(b)]
  rule <lambdak> I1:Int / I2:Int => I1 /Int I2   ... </lambdak> [tag(b)]
  rule <lambdak> I1:Int + I2:Int => I1 +Int I2   ... </lambdak> [tag(b)]
  rule <lambdak> I1:Int <= I2:Int => I1 <=Int I2 ... </lambdak> [tag(b)]

  rule <lambdak> if true  then E else _ => E ... </lambdak> [tag(b)]
  rule <lambdak> if false then _ else E => E ... </lambdak> [tag(b)]

  rule let X = E in E':Exp => (lambda X . E') E                         [macro, tag(b)]

  rule letrec F:Id X = E in E' => let F = mu F . lambda X . E in E'     [macro, tag(b)]

  syntax Exp ::= muclosure(Map,Exp)
  rule <lambdak> mu X . E => muclosure(Rho[X <- N], E) ...</lambdak>
       <lambdaenv> Rho </lambdaenv>
       <lambdastore>... .Map => (N:Int |-> muclosure(Rho[X <- N], E)) ...</lambdastore>
       <lambdacounter> N => N +Int 1 </lambdacounter>
       [tag(b), structural]
  rule <lambdak> muclosure(Rho,E) => E ~> Rho' ...</lambdak>
       <lambdaenv> Rho' => Rho </lambdaenv>
       [tag(b)]
endmodule
