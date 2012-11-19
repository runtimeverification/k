require "modules/substitution.k"
require "modules/unification.k"

module LAMBDA
  imports SUBSTITUTION
  imports UNIFICATION // * (UnificationVar => TypeVar) // renaming comming soon

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

  syntax TypeVar ::= "dummy"
  syntax Type ::= "int" | "bool"
                | Type "->" Type                  [strict]
                | "(" Type ")"                    [bracket]
                | TypeVar
  syntax UnificationVar ::= TypeVar

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
  rule lambda X . E => Tv -> E[Tv/X]  when fresh(Tv:TypeVar)
  rule T1:Type T2:Type => T1 = (T2 -> Tv) ~> Tv  when fresh(Tv:TypeVar)
  rule if T:Type then T1:Type else T2:Type => T = bool ~> T1 = T2 ~> T1
  rule let X = E in E' => E'[E/X]                                       
  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'        [macro]
  rule mu X . E => (Tv -> Tv) E[Tv/X]  when fresh(Tv:TypeVar)

  syntax K ::= Type "=" Type
  rule <k> T = T' => . ...</k>  <mgu> Theta:Mgu => updateMgu(Theta,T,T') </mgu>
  rule <k> T:Type => applyMgu(Theta,T) </k>  (<mgu> Theta:Mgu </mgu> => .)
endmodule
