// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module LAMBDA
  imports DOMAINS

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"                      [bracket]
               | Exp Exp                          [left]
               > Exp "*" Exp                      [left]
               | Exp "/" Exp
               > Exp "+" Exp                      [left]
               > Exp "<=" Exp
               > "lambda" Id "." Exp
               | "if" Exp "then" Exp "else" Exp
               | "let" Id "=" Exp "in" Exp        [macro]
               | "letrec" Id Id "=" Exp "in" Exp  [macro]
               | "mu" Id "." Exp

  syntax Type ::= "int" | "bool"
                | Type "->" Type
                | "(" Type ")"                    [bracket]

  syntax Exp ::= Type
  syntax KResult ::= Type

  configuration <tasks color="yellow">
                  <task color="orange" multiplicity="*" type="List">
                    <k color="green"> $PGM:Exp </k>
                    <tenv color="red"> .Map </tenv>
                  </task>
                </tasks>

  rule _I:Int => int
  rule _B:Bool => bool
  rule <k> X:Id => T ...</k>  <tenv>... X |-> T ...</tenv>

  rule <k> E1 * E2 => int ...</k> <tenv> Rho </tenv>
       (.Bag => <task> <k> E1 = int </k> <tenv> Rho </tenv> </task>
             <task> <k> E2 = int </k> <tenv> Rho </tenv> </task>)
  rule <k> E1 / E2 => int ...</k> <tenv> Rho </tenv>
       (.Bag => <task> <k> E1 = int </k> <tenv> Rho </tenv> </task>
             <task> <k> E2 = int </k> <tenv> Rho </tenv> </task>)
  rule <k> E1 + E2 => int ...</k> <tenv> Rho </tenv>
       (.Bag => <task> <k> E1 = int </k> <tenv> Rho </tenv> </task>
             <task> <k> E2 = int </k> <tenv> Rho </tenv> </task>)
  rule <k> E1 <= E2 => bool ...</k> <tenv> Rho </tenv>
       (.Bag => <task> <k> E1 = int </k> <tenv> Rho </tenv> </task>
             <task> <k> E2 = int </k> <tenv> Rho </tenv> </task>)

  rule <k> lambda X . E => ?Tx:Type -> ?Te:Type ...</k> <tenv> TEnv </tenv>
       (.Bag => <task> <k> E = ?Te </k> <tenv> TEnv[X <- ?Tx] </tenv> </task>)

  rule <k> E1 E2 => ?T:Type ...</k> <tenv> Rho </tenv>
       (.Bag => <task> <k> E1 = ?T2 -> ?T </k> <tenv> Rho </tenv> </task>
             <task> <k> E2 = ?T2:Type </k> <tenv> Rho </tenv> </task>)

  rule <k> if E then E1 else E2 => ?T:Type ...</k> <tenv> Rho </tenv>
       (.Bag => <task> <k> E = bool </k> <tenv> Rho </tenv> </task>
             <task> <k> E1 = ?T </k> <tenv> Rho </tenv> </task>
             <task> <k> E2 = ?T </k> <tenv> Rho </tenv> </task>)

  rule let X = E in E' => (lambda X . E') E
  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'
  rule <k> mu X . E => ?T:Type ...</k>  <tenv> TEnv </tenv>
       (.Bag => <task> <k> E = ?T </k> <tenv> TEnv[X <- ?T] </tenv> </task>)

  syntax KItem ::= Exp "=" Exp  [seqstrict]
  rule <k> T:Type = T:Type => .K ...</k>

  rule <task>... <k> .K </k> ...</task> => .Bag
endmodule
