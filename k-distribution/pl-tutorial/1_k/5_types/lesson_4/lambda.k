// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

// NOTE: this definition is not up to date with the latest version of K, as it
// uses both substitution and symbolic reasoning.
// It is intended for documentation and academic purposes only.

require "substitution.md"

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
               | "let" KVar "=" Exp "in" Exp        [macro, binder]
               | "letrec" KVar KVar "=" Exp "in" Exp  [macro, binder]
               | "mu" KVar "." Exp                  [binder]

  syntax Type ::= "int" | "bool"
                | Type "->" Type                  [klabel(functionType)]
                | "(" Type ")"                    [bracket]

  syntax Exp ::= Type
  syntax KResult ::= Type

  configuration <k color="green"> $PGM:Exp </k>

  rule _I:Int => int
  rule _B:Bool => bool
  rule T1:Type  * T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  / T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  + T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type <= T2:Type => T1 = int ~> T2 = int ~> bool

  syntax Exp ::= Exp "->" Exp                  [strict, klabel(functionType)]
  rule lambda X . E => ?T:Type -> (E[?T/X])

  rule T1:Type T2:Type => T1 = (T2 -> ?T:Type) ~> ?T
  rule if T:Type then T1:Type else T2:Type => T = bool ~> T1 = T2 ~> T1
  rule let X = E in E' => (lambda X . E') E
  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'
  rule mu X . E => (?T:Type -> ?T) (E[?T/X])

  syntax KItem ::= Type "=" Type
  rule T = T => .
endmodule
