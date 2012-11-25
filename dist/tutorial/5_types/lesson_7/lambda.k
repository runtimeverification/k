require "modules/unification.k"
require "modules/substitution.k"

module LAMBDA
  imports UNIFICATION
  imports SUBSTITUTION

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"                      [bracket]
               | Exp Exp                          [strict, left]
               > Exp "*" Exp                      [strict, left]
               | Exp "/" Exp                      [strict]
               > Exp "+" Exp                      [strict, left]
               > Exp "<=" Exp                     [strict]
               > "lambda" Id "." Exp
               | "if" Exp "then" Exp "else" Exp   [strict]
               | "let" Id "=" Exp "in" Exp        [strict(2)]
               | "letrec" Id Id "=" Exp "in" Exp
               | "mu" Id "." Exp

// get rid of dummy
  syntax TypeVar ::= "dummy"
  syntax Type ::= "int" | "bool"
                | Type "->" Type                  [strict]
                | "(" Type ")"                    [bracket]
                | TypeVar
// get rid of next
  syntax UnificationVar ::= TypeVar

  syntax TypeSchema ::= "forall" Set "." Type [binder, latex(\forall{#1}.{#2})]

  syntax Exp ::= Type
  syntax KResult ::= Type

  configuration <k color="green"> $PGM:Exp </k>
                <tenv color="red"> .Map </tenv>
                <mgu color="blue"> .Mgu </mgu>

  rule I:Int => int
  rule B:Bool => bool
  rule <k> X:Id => T ...</k>  <tenv>... X |-> T:Type ...</tenv>
  rule T1:Type  * T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  / T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  + T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type <= T2:Type => T1 = int ~> T2 = int ~> bool
  rule <k> lambda X:Id . E:Exp => Tv -> E ~> tenv(TEnv) ...</k>
       <tenv> TEnv:Map => TEnv[Tv/X] </tenv>  when fresh(Tv:TypeVar)
  rule T1:Type T2:Type => T1 = (T2 -> Tv) ~> Tv  when fresh(Tv:TypeVar)
  rule if T:Type then T1:Type else T2:Type => T = bool ~> T1 = T2 ~> T1

  rule <k> let X = T:Type in E => E ~> tenv(TEnv) ...</k>
       <mgu> Theta:Mgu </mgu>
       <tenv> TEnv:Map
        => TEnv[(forall freeVariables(applyMgu(Theta, T)) -Set
                        freeVariables(applyMguSet(Theta, values TEnv))
                . applyMgu(Theta, T)) / X]
       </tenv>
  rule <k> X:Id => freshVariables(Tvs,T) ...</k>
       <tenv>... X |-> forall Tvs . T ...</tenv>

  syntax K ::= freshVariables(Set,Type)
  rule freshVariables(.Set, T:Type) => T
  rule freshVariables(SetItem(Tv:TypeVar) S:Set, T:Type)
    => freshVariables(S, T[Tv'/Tv])
    when fresh(Tv':TypeVar)

  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'        [macro]
  rule <k> mu X:Id . E:Exp => (Tv -> Tv) E ~> tenv(TEnv) ...</k>
          <tenv> TEnv:Map => TEnv[Tv/X] </tenv>
    when fresh(Tv:TypeVar)

  syntax K ::= Type "=" Type
  rule <k> T = T' => . ...</k>  <mgu> Theta:Mgu => updateMgu(Theta,T,T') </mgu>
  rule <k> T:Type => applyMgu(Theta,T) </k>  (<mgu> Theta:Mgu </mgu> => .)

  syntax K ::= tenv(Map)
  rule <k> T:Type ~> (tenv(TEnv) => .) ...</k>  <tenv> _ => TEnv </tenv>
endmodule
