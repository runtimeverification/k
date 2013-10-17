//@ \section{Syntax}

module IMP-SYNTAX

  syntax AExp ::= Int | Id
                | AExp "/" AExp    [left, strict]
                | AExp "*" AExp    [left, strict]
                > AExp "+" AExp    [left, strict]
                | "(" AExp ")"     [bracket]
  syntax BExp ::= Bool
                | AExp "<=" AExp   [seqstrict, latex({#1}\leq{#2})]
                | "not" BExp       [strict]
                > BExp "and" BExp  [left, strict(1)]
                | "(" BExp ")"     [bracket]
  syntax Stmt ::= "skip"
                | Id ":=" AExp     [strict(2)]
                | "if" BExp
                  "then" Stmt
                  "else" Stmt      [strict(1)]
                | "while" BExp
                  "do" Stmt
                | "for" Id "from" AExp "to" AExp "do" Stmt
                                   [strict(2 3)] 
                > Stmt ";" Stmt    [left]
                | "(" Stmt ")"     [bracket]


  syntax Pgm ::= "var" Ids ";" Stmt
  syntax Ids ::= List{Id,","}

endmodule

//@ \section{Semantics}

module IMP
  imports IMP-SYNTAX

/*@ \subsection{Values and results}
*/
  syntax KResult ::= Int | Bool



/*@ \subsection{Configuration}
*/
  configuration <T color="yellow">
                  <k color="green"> $PGM:K </k>
                  <state color="red"> .Map </state>
                </T>

/*@ \subsection{Arithmetic expressions}
*/
  rule [lookup]: <k> X:Id => I ...</k> <state>... X |-> I ...</state>

  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0 

  rule I1:Int <= I2:Int => I1 <=Int I2
  rule not(T:Bool) => notBool T
  rule true and B:BExp => B
  rule false and _ => false

/*@ \subsection{Statements}

/*@ \subsubsection{Skip}
*/

  rule [skip]: skip => .

/*@ \subsubsection{Assignment}
*/

  rule [assignment]:
    <k> X := I:Int => . ...</k> <state>... X|->(_ => I) ...</state>

/*@ \subsubsection{Sequential composition}

*/

  rule [sequential]: S1 ; S2 => S1 ~> S2  [structural]

/*@ \subsubsection{Conditional}
 */

  rule [if-true]:  if true then S else _ => S
  rule [if-false]: if false then _ else S => S

/*@ \subsubsection{While loop}
*/

  rule [while]:
       while B do S
       =>
       if B then (S ; while B do S) else skip
       [structural]

  rule [for]: 
       for I:Id from A1:Int to A2:Int do S:Stmt
       => 
       I := A1;
       if (I <= A2) then (S; for I from (A1 + 1) to A2  do S)
                    else skip
       [structural]

/*@ \subsection{Programs}

*/

  rule [program-still-vars]:
       <k> var (X:Id,Xs:Ids => Xs); _ </k>
       <state> Rho:Map (. => X |-> 0) </state>
       when notBool(X in keys(Rho))

  rule [program-no-vars]:
       <k> var .Ids; S => S </k>
       [structural]
endmodule
