// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "modules/substitution.k"
require "modules/unification.k"

module LAMBDA
  imports SUBSTITUTION
  imports UNIFICATION

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"                      [bracket]
               | Exp Exp                          [strict, left]
               > Exp "*" Exp                      [strict, left]
               | Exp "/" Exp                      [strict]
               > Exp "+" Exp                      [strict, left]
               > Exp "<=" Exp                     [strict]
               > "lambda" Id "." Exp              [binder]
               | "if" Exp "then" Exp "else" Exp   [strict]
               | "let" Id "=" Exp "in" Exp        [binder]
               | "letrec" Id Id "=" Exp "in" Exp  [binder]
               | "mu" Id "." Exp                  [binder]

  syntax Type ::= "int" | "bool"
                | Type "->" Type
                | "(" Type ")"                    [bracket]

  syntax Exp ::= Type
  syntax KResult ::= Type

  configuration <k color="green"> $PGM:Exp </k>
                <mgu color="blue"> .Mgu </mgu>

  rule I:Int => int
  rule B:Bool => bool
  rule T1:Type  * T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  / T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  + T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type <= T2:Type => T1 = int ~> T2 = int ~> bool
  syntax Exp ::= Exp "->" Exp  [strict]

  rule lambda X . E:Exp => ?T:Type -> E[?T/X]
  rule T1:Type T2:Type => T1 = (T2 -> ?T:Type) ~> ?T
  rule if T:Type then T1:Type else T2:Type => T = bool ~> T1 = T2 ~> T1
  rule let X = E in E' => E'[E/X]                                       [macro]
  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'        [macro]
  rule mu X . E => (?T:Type -> ?T) E[?T/X]

  syntax KItem ::= Type "=" Type
  rule <k> T = T' => . ...</k>  <mgu> Theta:Mgu => updateMgu(Theta,T,T') </mgu>
  rule <k> T:Type => applyMgu(Theta,T) </k>  <mgu> Theta:Mgu => . </mgu>
endmodule
