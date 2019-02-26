// Copyright (c) 2012-2019 K Team. All Rights Reserved.

require "substitution.k"

module LAMBDA
  imports DOMAINS
  imports SUBSTITUTION

  syntax Exp ::= Int | Bool | KVar
               | "(" Exp ")"                      [bracket]
               | Exp Exp                          [strict, left]
               > Exp "*" Exp                      [strict, left]
               | Exp "/" Exp                      [strict]
               > Exp "+" Exp                      [strict, left]
               > Exp "<=" Exp                     [strict]
               > "lambda" KVar "." Exp              [binder]
               | "if" Exp "then" Exp "else" Exp   [strict]
               | "let" KVar "=" Exp "in" Exp
               | "letrec" KVar KVar "=" Exp "in" Exp
               | "mu" KVar "." Exp                  [binder]

  syntax Type ::= "int" | "bool"
                | Type "->" Type
                | "(" Type ")"                    [bracket]

  syntax Exp ::= Type
  syntax KResult ::= Type

  configuration <k color="green"> $PGM:Exp </k>
                <tenv color="red"> .Map </tenv>

  rule I:Int => int
  rule B:Bool => bool
  rule <k> X:KVar => T ...</k>  <tenv>... X |-> T ...</tenv>
  rule T1:Type  * T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  / T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  + T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type <= T2:Type => T1 = int ~> T2 = int ~> bool

  syntax Exp ::= Exp "->" Exp                  [strict]
  rule <k> lambda X:KVar . E => ?T:Type -> E ~> setTenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[X <- ?T] </tenv>

  rule T1:Type T2:Type => T1 = (T2 -> ?T:Type) ~> ?T
  rule if T:Type then T1:Type else T2:Type => T = bool ~> T1 = T2 ~> T1
  rule let X = E in E' => E'[E/X]                                       [macro]
  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'        [macro]
  rule <k> mu X:KVar . E:Exp => (?T:Type -> ?T) E ~> setTenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[X <- ?T] </tenv>

  syntax KItem ::= Type "=" Type
  rule T = T => .

  syntax KItem ::= setTenv(Map)
  rule <k> T:Type ~> (setTenv(TEnv) => .) ...</k>  <tenv> _ => TEnv </tenv>
endmodule
