requires "substitution.md"

module LAMBDA-SYNTAX
  imports ID-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Val  ::= Int | Bool

  syntax Exp  ::= Id
                | Val
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
                  | cc(K, Map)

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

  rule  <k> - I:Int          => 0   -Int I ...</k>
  rule  <k> I1:Int *  I2:Int => I1  *Int I2 ...</k>
  rule  <k> I1:Int /  I2:Int => I1  /Int I2 ...</k>
  rule  <k> I1:Int +  I2:Int => I1  +Int I2 ...</k>

  rule  <k> I1:Int <= I2:Int => I1 <=Int I2 ...</k>

  rule  <k> if true  then E else _ => E ...</k>
  rule  <k> if false then _ else E => E ...</k>

  rule  <k> let V = E1 in E2 => (lambda V . E2) E1 ...</k>

  rule  <k> letrec F:Id X = E in E' => let F = mu F . lambda X . E in E' ...</k>

  syntax Exp  ::= muclosure(Exp, Map)

  rule  <k> mu X . E => muclosure(E, Rho[X <- !N]) ...</k>
        <env> Rho </env>
        <store>... .Map => (!N:Int |-> muclosure(E, Rho[X <- !N])) ...</store>

  rule  <k> muclosure(E, Rho) => E ~> Rho' ...</k>
        <env> Rho' => Rho </env>

  rule  <k> (callcc V:Val => V cc(K, Rho)) ~> K </k>
        <env> Rho </env>

  rule  <k> cc(K, Rho) V ~> _ => V ~> K </k>
        <env> _ => Rho </env>
endmodule
