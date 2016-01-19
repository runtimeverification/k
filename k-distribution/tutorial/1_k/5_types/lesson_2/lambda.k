// Copyright (c) 2012-2016 K Team. All Rights Reserved.

require "substitution.k"

module LAMBDA
  imports SUBSTITUTION

  syntax Type ::= "int" | "bool"
                | Type "->" Type
                | "(" Type ")"                 [bracket]

  syntax Exp ::= Id
               | "lambda" Id ":" Type "." Exp  [binder]
               | Exp Exp                       [strict, left]
               | "(" Exp ")"                   [bracket]

  syntax Exp ::= Type

  syntax KVariable ::= Id

  syntax KResult ::= Type

  syntax Exp ::= Exp "->" Exp                  [strict]

  rule lambda X : T . E => T -> E[T/X]
  rule (T1 -> T2) T1 => T2

  syntax Exp ::= Int | Bool
               | Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]

  rule _:Int => int
  rule _:Bool => bool
  rule int * int => int
  rule int / int => int
  rule int + int => int
  rule int <= int => bool

  syntax Exp ::= "if" Exp "then" Exp "else" Exp                       [strict]
  rule if bool then T:Type else T => T

  syntax Exp ::= "let" Id ":" Type "=" Exp "in" Exp
  rule let X : T = E in E' => (lambda X : T . E') E                   [macro]

  syntax Exp ::= "letrec" Id ":" Type Id ":" Type "=" Exp "in" Exp
               | "mu" Id ":" Type "." Exp                             [binder]
  rule letrec F : T1  X : T2 = E in E'
    => let F : T1 = mu F : T1 . lambda X : T2 . E in E'               [macro]
  rule mu X : T . E => (T -> T) (E[T/X]):>Exp  // TODO: casting should not be needed
endmodule
