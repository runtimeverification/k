// Copyright (c) 2012-2015 K Team. All Rights Reserved.

module LAMBDA

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"                      [bracket]
               | Exp Exp                          [strict, left]
               > Exp "*" Exp                      [strict, left]
               | Exp "/" Exp                      [strict]
               > Exp "+" Exp                      [strict, left]
               > Exp "<=" Exp                     [strict]
               > "lambda" Id "." Exp
               | "if" Exp "then" Exp "else" Exp   [strict]
               | "let" Id "=" Exp "in" Exp
               | "letrec" Id Id "=" Exp "in" Exp
               | "mu" Id "." Exp

  syntax Type ::= "int" | "bool"
                | Type "->" Type
                | "(" Type ")"                    [bracket]

  syntax Exp ::= Type
  syntax Variable ::= Id
  syntax KResult ::= Type

  configuration <k color="green"> $PGM:Exp </k>
                <tenv color="red"> .Map </tenv>

  rule I:Int => int
  rule B:Bool => bool
  rule <k> X:Id => T ...</k>  <tenv>... X |-> T ...</tenv>
  rule T1:Type  * T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  / T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  + T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type <= T2:Type => T1 = int ~> T2 = int ~> bool

  rule <k> lambda X:Id . E:Exp => E ~> ?T:Type -> HOLE ~> tenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[X <- ?T] </tenv>
  rule T2:Type ~> T1:Type -> HOLE => T1 -> T2
  rule T1:Type T2:Type => T1 = (T2 -> ?T:Type) ~> ?T
  rule if T:Type then T1:Type else T2:Type => T = bool ~> T1 = T2 ~> T1
  rule let X = E in E' => (lambda X . E') E                             [macro]
  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'        [macro]
  rule <k> mu X:Id . E:Exp => (?T:Type -> ?T) E ~> tenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[X <- ?T] </tenv>

  syntax KItem ::= Type "=" Type
  rule T = T => .

  syntax KItem ::= tenv(Map)
  rule <k> T:Type ~> (tenv(TEnv) => .) ...</k>  <tenv> _ => TEnv </tenv>
endmodule
