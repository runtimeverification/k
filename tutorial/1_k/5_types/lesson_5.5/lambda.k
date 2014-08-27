// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module LAMBDA
  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"                        [bracket]
               | Exp Exp                            [left, seqstrict]
               > Exp "*" Exp                        [left, seqstrict]
               | Exp "/" Exp                        [left, seqstrict]
               > Exp "+" Exp                        [left, seqstrict]
               > Exp "-" Exp                        [left, seqstrict]
               > Exp "<=" Exp                       [seqstrict]
               > "if" Exp "then" Exp "else" Exp     [seqstrict]
               | "lambda" Id "." Exp
               | "mu" Id "." Exp
               | "let" Id "=" Exp "in" Exp          [strict(2)]
               | "letrec" Id Id "=" Exp "in" Exp
  syntax Type ::= "int" | "bool"
                | Type "->" Type                    [strict(2)]
                | "(" Type ")"                      [bracket]

  syntax Exp ::= Type
  syntax KResult ::= Type

  // macro is not supported yet
  // rule letrec F X = E in E' => let F = mu F . lambda X . E in E'    [macro]
  rule letrec F:Id X:Id = E:Exp in E':Exp => let F = mu F . lambda X . E in E'

  configuration <T color="yellow">
                  <k color="green"> $PGM:Exp </k>
                  <tenv color="red"> .Map </tenv>
                </T>

  rule I:Int => int
  rule B:Bool => bool
  rule <k> X:Id => T ...</k> <tenv>... X |-> T:Type ...</tenv>
  rule (T1:Type -> T2:Type) T1 => T2
  rule int * int => int
  rule int / int => int
  rule int + int => int
  rule int - int => int
  rule int <= int => bool
  rule if bool then T:Type else T => T
  syntax KItem ::= env(Map)
  rule <k> lambda X:Id . E:Exp => ?T:Type -> (E)::K ~> env(TEnv) ...</k>
       <tenv> TEnv:Map => TEnv[X <- ?T] </tenv>
  rule <k> mu X:Id . E:Exp => (?T:Type -> ?T) E ~> env(TEnv) ...</k>
       <tenv> TEnv:Map => TEnv[X <- ?T] </tenv>

  rule let X = E in E' => (lambda X . E') E

  rule <k> T:Type ~> (env(TEnv:Map) => .) ...</k> <tenv> _:Map => TEnv </tenv>
endmodule

