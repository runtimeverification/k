requires "substitution.md"

module LAMBDA-SYNTAX
  imports ID-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Val  ::= Int | Bool

  syntax Exp  ::= Id
                | "lambda" Id "." Exp
                | "-" Int
                | Exp Exp [left, strict]
                | "(" Exp ")" [bracket]

  syntax Exp  ::= Exp "*"  Exp [strict, left]
                | Exp "/"  Exp [strict, left]
                > Exp "+"  Exp [strict, left]
                > Exp "<=" Exp [strict]

  syntax Exp  ::= "if" Exp "then" Exp "else" Exp [strict(1)]

  syntax Exp  ::= "let" Id "=" Exp "in" Exp
                | "mu" Id "." Exp
                | "letrec" Id Id "=" Exp "in" Exp

  syntax Exp  ::= "callcc" Exp [strict]

  syntax Val  ::= cc(K)
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS

  syntax KResult ::= Val

  configuration
    <T>
      <k> $PGM:Exp </k>
      <env> .Map </env>
      <store> .Map </store>
    </T>

  syntax Val    ::= closure(Map, Id, Exp)
  syntax Exp    ::= Val

  rule  <k> lambda X:Id . E:Exp => closure(Rho, X, E) ...</k>
        <env> Rho </env>

  rule  <k> closure(Rho, X, E) V:Val => E ~> Rho' ...</k>
        <env> Rho' => Rho[X <- !N] </env>
        <store>... .Map => (!N:Int |-> V) ...</store>

  rule  <k> X:Id => V ...</k>
        <env>... X |-> N ...</env>
        <store>... N |-> V ...</store>

  rule  <k> _:Val ~> (Rho => .) ... </k>
        <env> _ => Rho </env>
endmodule
