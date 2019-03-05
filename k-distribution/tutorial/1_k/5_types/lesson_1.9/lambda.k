// Copyright (c) 2013-2019 K Team. All Rights Reserved.

require "substitution.k"

module LAMBDA
  imports DOMAINS
  imports SUBSTITUTION

  syntax Type ::= "int" | "bool"
                | Type "->" Type
                | "(" Type ")"                 [bracket]

  syntax Exp ::= KVar
               | "lambda" KVar ":" Type "." Exp  [binder]
               | Exp Exp                       [left]
               | "(" Exp ")"                   [bracket]

  syntax Exp ::= Type

  syntax KResult ::= Type

  syntax Exp ::= Exp "->" Exp
  rule lambda X : T . E => T -> (E[T/X])       [anywhere]
  rule (T1 -> T2) T1 => T2                     [anywhere]

  syntax Exp ::= Int                           [klabel(intConst), prefer]
               | Bool                          [klabel(boolConst), prefer]
               | Exp "*" Exp                   [left]
               | Exp "/" Exp
               > Exp "+" Exp                   [left]
               > Exp "<=" Exp

  rule _:Int => int                            [anywhere]
  rule _:Bool => bool                          [anywhere]
  rule int * int => int                        [anywhere]
  rule int / int => int                        [anywhere]
  rule int + int => int                        [anywhere]
  rule int <= int => bool                      [anywhere]

  syntax Exp ::= "if" Exp "then" Exp "else" Exp
  rule if bool then T:Type else T => T         [anywhere]

  syntax Exp ::= "let" KVar ":" Type "=" Exp "in" Exp
  rule let X : T = E in E' => (lambda X : T . E') E                   [macro]

  syntax Exp ::= "letrec" KVar ":" Type KVar ":" Type "=" Exp "in" Exp
               | "mu" KVar ":" Type "." Exp      [binder]
  rule letrec F : T1  X : T2 = E in E'
    => let F : T1 = mu F : T1 . lambda X : T2 . E in E'               [macro]
  rule mu X : T . E => (T -> T) (E[T/X])         [anywhere]
endmodule
