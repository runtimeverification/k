require "modules/unification.k"

module LAMBDA
  imports UNIFICATION

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"                      [bracket]
               | Exp Exp                          [left]
               > Exp "*" Exp                      [left]
               | Exp "/" Exp
               > Exp "+" Exp                      [left]
               > Exp "<=" Exp
               > "lambda" Id "." Exp
               | "if" Exp "then" Exp "else" Exp
               | "let" Id "=" Exp "in" Exp
               | "letrec" Id Id "=" Exp "in" Exp
               | "mu" Id "." Exp

  syntax Type ::= "int" | "bool"
                | Type "->" Type
                | "(" Type ")"                    [bracket]

  syntax Exp ::= Type

  syntax KResult ::= Type

  configuration <tasks color="yellow">
                  <task color="orange" multiplicity="*">
                    <k color="green"> $PGM:Exp </k>
                    <tenv color="red"> .Map </tenv>
                  </task>
                </tasks>
                <mgu color="blue"> .Mgu </mgu>

  rule I:Int => int
  rule B:Bool => bool
  rule <k> X:Id => T ...</k>  <tenv>... X |-> T ...</tenv>

  rule <k> E1 * E2 => int ...</k> <tenv> Rho </tenv>
       (. => <task> <k> E1 = int </k> <tenv> Rho </tenv> </task> <br/>
             <task> <k> E2 = int </k> <tenv> Rho </tenv> </task>)
  rule <k> E1 / E2 => int ...</k> <tenv> Rho </tenv>
       (. => <task> <k> E1 = int </k> <tenv> Rho </tenv> </task> <br/>
             <task> <k> E2 = int </k> <tenv> Rho </tenv> </task>)
  rule <k> E1 + E2 => int ...</k> <tenv> Rho </tenv>
       (. => <task> <k> E1 = int </k> <tenv> Rho </tenv> </task> <br/>
             <task> <k> E2 = int </k> <tenv> Rho </tenv> </task>)
  rule <k> E1 <= E2 => bool ...</k> <tenv> Rho </tenv>
       (. => <task> <k> E1 = int </k> <tenv> Rho </tenv> </task> <br/>
             <task> <k> E2 = int </k> <tenv> Rho </tenv> </task>)

  rule <k> lambda X . E => Tx -> Te ...</k> <tenv> TEnv </tenv>
       (. => <task> <k> E = Te </k> <tenv> TEnv[Tx/X] </tenv> </task>)
    when fresh(Tx:Type) andBool fresh(Te:Type)

  rule <k> E1 E2 => T ...</k> <tenv> Rho </tenv>
       (. => <task> <k> E1 = T2 -> T </k> <tenv> Rho </tenv> </task> <br/>
             <task> <k> E2 = T2 </k> <tenv> Rho </tenv> </task>)
    when fresh(T2:Type) andBool fresh(T:Type)

  rule <k> if E then E1 else E2 => T ...</k> <tenv> Rho </tenv>
       (. => <task> <k> E = bool </k> <tenv> Rho </tenv> </task> <br/>
             <task> <k> E1 = T </k> <tenv> Rho </tenv> </task>   <br/>
             <task> <k> E2 = T </k> <tenv> Rho </tenv> </task>)
    when fresh(T:Type)

  rule let X = E in E' => (lambda X . E') E                             [macro]
  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'        [macro]
  rule <k> mu X . E => T ...</k>  <tenv> TEnv </tenv>
       (. => <task> <k> E = T </k> <tenv> TEnv[T/X] </tenv> </task>)
    when fresh(T:Type)

  syntax K ::= Exp "=" Exp  [strict]
  rule <k> T:Type = T':Type => . ...</k>
       <mgu> Theta:Mgu => updateMgu(Theta,T,T') </mgu>
  rule <tasks> <task> <k> T:Type => applyMgu(Theta,T) </k> ...</task> </tasks>
       <mgu> Theta:Mgu => . </mgu>

  rule <task>... <k> . </k> ...</task> => .
endmodule
