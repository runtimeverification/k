module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Type ::= "int"
                | "bool"
                | Type "->" Type
                | "(" Type ")" [bracket]

  syntax Exp  ::= Id
                | "lambda" Id ":" Type "." Exp
                | Exp Exp [strict, left]
                | "(" Exp ")" [bracket]

  syntax Exp  ::= Int | Bool
                | "-" Int
                > Exp "*"  Exp [strict, left]
                | Exp "/"  Exp [strict, left]
                > Exp "+"  Exp [strict, left]
                > Exp "<=" Exp [strict]

  syntax Exp  ::= "if" Exp "then" Exp "else" Exp [strict]

  syntax Exp  ::= "let" Id ":" Type "=" Exp "in" Exp
                | "mu"  Id ":" Type "." Exp
                | "letrec" Id ":" Type Id ":" Type "=" Exp "in" Exp
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS

  configuration
    <T>
      <k> $PGM:Exp </k>
      <tenv> .Map </tenv>
    </T>

  syntax KResult  ::= Type

  syntax Exp      ::= Type
                    | Exp "->" Exp [strict]

  rule  <k> lambda X : T . E => (T -> E) ~> Rho ...</k>
        <tenv> Rho => Rho [X <- T] </tenv>

  rule (T -> T') T => T'

  rule  <k> X:Id => T ...</k>
        <tenv>... X |-> T ...</tenv>

  rule _:Int => int
  rule _:Bool => bool

  rule - _ => int
  rule int *  int => int
  rule int /  int => int
  rule int +  int => int
  rule int <= int => bool

  rule if bool then T:Type else T => T

  rule let V : T = E1 in E2 => (lambda V : T . E2) E1 [macro]

  /* rule letrec F : T X : T' = E in E' => */
  /*   let F : T = mu F : T . lambda X : T' . E in E' [macro] */

  /* rule mu X : T . E => (T -> T):Type (E [T / X]) */

  rule  <k> _ ~> (Rho => .) ...</k>
        <tenv> _ => Rho </tenv>
endmodule
