require "builtins/map.k"
require "builtins/meta-k.k"


module LAMBDA
  imports MAP
  imports META-K

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"                        [bracket]
               | Exp Exp                            [left, strict]
               > Exp "*" Exp                        [left, strict]
               | Exp "/" Exp                        [left, strict]
               > Exp "+" Exp                        [left, strict]
               > Exp "-" Exp                        [left, strict]
               > Exp "<=" Exp                       [strict]
               > "if" Exp "then" Exp "else" Exp     [strict]
               | "lambda" Id "." Exp
               | "mu" Id "." Exp
               | "let" Id "=" Exp "in" Exp          [strict(2)]
               | "letrec" Id Id "=" Exp "in" Exp
  syntax Type ::= "int" | "bool"
                | Type "->" Type                    [strict(2)]
                | "(" Type ")"                      [bracket]
  syntax TypeSchema ::= "forall" MySet "." Type     [klabel(schema)]

  syntax Exp ::= Type
  syntax KResult ::= Type

  // macro is not supported yet
  // rule letrec F X = E in E' => let F = mu F . lambda X . E in E'    [macro]
  rule letrec F:Id X:Id = E:Exp in E':Exp => let F = mu F . lambda X . E in E'


  configuration <T color="yellow">
                  <k color="green"> $PGM:Exp </k>
                  <tenv color="red"> .MyMap </tenv>
                </T>


  rule I:Int => int
  rule B:Bool => bool
  rule <k> X:Id => T ...</k> <tenv>... X |-> T:Type ...</tenv>
  rule <k> X:Id => #rename(T, S) ...</k>
       <tenv>... X |-> forall S:MySet . T:Type ...</tenv>
  rule (T1:Type -> T2:Type) T1 => T2
  rule int * int => int
  rule int / int => int
  rule int + int => int
  rule int - int => int
  rule int <= int => bool
  rule if bool then T:Type else T => T
  //rule <k> lambda X:Id . E:Exp => T:Type -> E::K ~> TEnv ...</k>
  rule <k> lambda X:Id . E:Exp => T:Type -> (E)::K ~> TEnv ...</k>
       <tenv> TEnv:MyMap => TEnv[X <- T] </tenv>
  rule <k> mu X:Id . E:Exp => (T:Type -> T) E ~> TEnv ...</k>
       <tenv> TEnv:MyMap => TEnv[X <- T] </tenv>
  rule <k> let X:Id = T:Type in E:Exp => E ~> TEnv ...</k>
       <tenv>
         TEnv:MyMap
       =>
         TEnv[X <- forall #variables(T) -MySet #variables(TEnv) . T]
       </tenv>

  rule <k> T:Type ~> (TEnv:MyMap => .) ...</k> <tenv> _:MyMap => TEnv </tenv>
endmodule

