requires "substitution.md"

module LAMBDA-SYNTAX
  imports KVAR-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Type ::= "int"
                | "bool"
                | Type "->" Type
                | "(" Type ")" [bracket]

  syntax Exp  ::= KVar
                | "lambda" KVar ":" Type "." Exp [binder]
                | Exp Exp [strict, left]
                | "(" Exp ")" [bracket]

  syntax Exp  ::= Int | Bool
                | Exp "*"  Exp [strict, left]
                | Exp "/"  Exp [strict, left]
                > Exp "+"  Exp [strict, left]
                > Exp "<=" Exp [strict]

  syntax Exp  ::= "if" Exp "then" Exp "else" Exp [strict]

  syntax Exp  ::= "let" KVar ":" Type "=" Exp "in" Exp
                | "mu"  KVar ":" Type "." Exp [binder]
                | "letrec" KVar ":" Type KVar ":" Type "=" Exp "in" Exp
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS

  syntax KResult  ::= Type

  syntax Exp      ::= Type
                    | Exp "->" Exp [strict]

  rule lambda X : T . E => T -> (E[T / X])
  rule (T -> T') T => T'

  rule _:Int => int
  rule _:Bool => bool

  rule int *  int => int
  rule int /  int => int
  rule int +  int => int
  rule int <= int => bool

  rule if bool then T:Type else T => T

  rule let V : T = E1 in E2 => (lambda V : T . E2) E1 [macro]

  /* rule letrec F X = E in E' => */
  /*   let F = mu F . lambda X . E in E' [macro] */

  /* rule mu X . E => E[(mu X . E) / X] */

endmodule
