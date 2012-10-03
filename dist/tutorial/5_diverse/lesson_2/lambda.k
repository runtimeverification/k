require "modules/substitution.k"

module LAMBDA
  imports SUBSTITUTION

  syntax Type ::= "int" | "bool"
                | Type "->" Type  [strict]
                | "(" Type ")"    [bracket]

  syntax Exp ::= Id
               | "lambda" Id ":" Type "." Exp  [binder(1)]
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
  syntax Exp ::= Type

  syntax KResult ::= Type

  rule lambda X:Id : T . E:Exp => T -> E[T / X]
  rule (T1:Type -> T2:Type) T1 => T2

  syntax Exp ::= Int | Bool
               | Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
  rule int * int => int
  rule int / int => int
  rule int + int => int
  rule int <= int => bool

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict]
  rule if bool  then T:Type else T => T

  syntax Exp ::= "let" Id ":" Type "=" Exp "in" Exp
  rule let X : T = E in E':Exp => (lambda X : T . E') E
    [structural]

  syntax Exp ::= "letrec" Id ":" Type Id ":" Type "=" Exp "in" Exp
               | "mu" Id ":" Type "." Exp      [binder(1)]
  rule letrec F:Id : T1:Type X : T2:Type = E in E'
    => let F : T1 = mu F : T1 . lambda X : T2 . E in E'
    [structural]
  rule mu X : T:Type . E => (T -> T) E[T / X]
endmodule
