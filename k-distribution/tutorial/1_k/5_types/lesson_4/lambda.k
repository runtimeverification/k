// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "modules/substitution-java.k"

module LAMBDA
  imports SUBSTITUTION

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
                | Type "->" Type                  [smtlib(funcType)]
                | "(" Type ")"                    [bracket]

  syntax Exp ::= Type
  syntax Variable ::= Id
  syntax KResult ::= Type

  configuration <k color="green"> $PGM:Exp </k>

  rule I:Int => int
  rule B:Bool => bool
  rule int * int => int
  rule int / int => int
  rule int + int => int
  rule int <= int => bool

  rule lambda X . E:Exp => E[?T/X] ~> ?T:Type -> HOLE
  rule T2:Type ~> T1:Type -> HOLE => T1 -> T2
  rule (T1:Type -> T2:Type) T1 => T2
  rule if bool then T:Type else T => T
  rule let X = E in E' => (lambda X . E') E                             [macro]
  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'        [macro]
  rule mu X . E => (?T:Type -> ?T) (E[?T/X])

  rule T1 -> T2 =/=K T1 => true [smt-lemma]

endmodule
