// This currently does not work.  It would work if we had unification builtin
// for symbolic variables.  That would be awesome!


module LAMBDA
  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"                      [bracket]
               | !Exp !Exp                        [left]
               > !Exp "*" !Exp                    [left]
               | !Exp "/" !Exp
               > !Exp "+" !Exp                    [left]
               > !Exp "<=" !Exp
               > "lambda" Id "." Exp
               | "if" !Exp "then" !Exp "else" !Exp
               | "let" Id "=" !Exp "in" Exp
               | "letrec" Id Id "=" Exp "in" Exp
               | "mu" Id "." Exp

  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'        [macro]

  syntax Type ::= "int" | "bool"
                | Type "->" !Type
                | "(" Type ")"                    [bracket]

  syntax TypeSchema ::= "forall" Set "." Type [binder]

  syntax Exp ::= Type
  syntax KResult ::= Type

  configuration <k color="green"> $PGM:Exp </k>
                <tenv color="red"> .Map </tenv>

  rule I:Int => int
  rule B:Bool => bool
  rule <k> X:Id => T ...</k>  <tenv>... X |-> T:Type ...</tenv>
  rule int * int => int
  rule int / int => int
  rule int + int => int
  rule int <= int => bool
  rule <k> lambda X . E => T:Type -> E ~> tenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[T/X] </tenv>
  rule (T1:Type -> T2:Type) T1 => T2
  rule if bool then T else T => T:Type
  rule <k> let X = T:Type in E => E ~> tenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[(forall FV(T) -Set FV(values TEnv) . T) / X] </tenv>
  rule <k> X:Id => freshVariables(Tvs,T) ...</k>
       <tenv>... X |-> forall Tvs . T ...</tenv>
  rule <k> mu X . E => (T:Type -> T) E ~> tenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[T/X] </tenv>

  syntax K ::= tenv(Map)
  rule <k> T:Type ~> (tenv(TEnv) => .) ...</k>  <tenv> _ => TEnv </tenv>
endmodule
