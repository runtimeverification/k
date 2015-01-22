// Copyright (c) 2012-2015 K Team. All Rights Reserved.
module LAMBDA
  syntax Type ::= "int" | "bool"
                | Type "->" Type
                | "(" Type ")"                 [bracket]

  syntax Exp ::= Id
               | "lambda" Id ":" Type "." Exp
               | Exp Exp                       [strict, left]
               | "(" Exp ")"                   [bracket]

  syntax Exp ::= Type

  syntax Variable ::= Id

  syntax KResult ::= Type

  configuration <T color="yellow">
                  <k color="green"> $PGM:Exp </k>
                  <tenv color="blue"> .Map </tenv>
                </T>

  syntax Exp ::= Exp "->" Exp                  [strict]
  rule <k> lambda X : T . E:Exp => (T -> E) ~> Rho ...</k>
       <tenv> Rho:Map => Rho[X <- T] </tenv>
  // Remove the sorting of E above when the bug is fixed.  Currently, the
  // inferred sort is Type, due to a bug.
  rule <k> X:Id => T ...</k> <tenv>... X |-> T ...</tenv>
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
               | "mu" Id ":" Type "." Exp
  rule letrec F : T1  X : T2 = E in E'
    => let F : T1 = mu F : T1 . lambda X : T2 . E in E'               [macro]
  rule <k> mu X : T . E => (T -> T) E ~> Rho ...</k>
       <tenv> Rho => Rho[X <- T] </tenv>

// Auxiliary type environment recovery
  rule <k> _:Type ~> (Rho => .) ...</k> <tenv> _ => Rho </tenv>
endmodule
