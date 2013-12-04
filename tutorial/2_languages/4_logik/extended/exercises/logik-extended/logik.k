require "modules/unification.k"

/*!
\title{LOGIK}
\author{Grigore Ro\c{s}u and Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
        (\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}
...
 */

module LOGIK
  imports UNIFICATION

  syntax Term ::= Variable | Literal | Literal "(" Terms ")"
  syntax Terms ::= List{Term,","}
  syntax Clause ::= Term ":-" Terms "." | Term "."
  syntax Query ::= "?-" Terms "."
  syntax Pgm ::= Query | Clause Pgm

  syntax Variable ::= Token{[\_A-Z][a-zA-Z0-9\_]*}               [onlyLabel]
  syntax Literal ::= Token{[a-z][a-zA-Z0-9\_]*}                  [onlyLabel]

  rule L. => L :- .Terms .                                       [macro]

  rule (X:Literal => X(.Terms)) :- _ .                           [macro]
  rule (X:Literal => X(.Terms)),_                                [macro]

  configuration <T color="yellow" multiplicity="?">
                  <k color="green"> $PGM:Pgm </k>
                  <fresh color="orange"> .K </fresh>
                  <mgu color="blue"> (.Mgu)::MguOrError </mgu>
                  <br/>
                  <clauses color="red">
                    <clause color="pink" multiplicity="*"> .K </clause>
                  </clauses>
                </T>
                <solution multiplicity="?"> .Map </solution>

  rule <k> C:Clause Pgm => Pgm </k>
       (. => <clause> C </clause>)

  rule ?- Ls:Terms. => Ls

  rule L:Term, Ls:Terms => L ~> Ls
  rule .Terms => .

  rule <T>... <k> . </k> <mgu> Theta:Mgu </mgu> ...</T>
    => <solution> Mgu2Map(Theta) </solution>

  rule <T>... <mgu> _:MguError </mgu> ...</T> => .

  rule <fresh> . => renameVariables(C) </fresh>  <clause> C </clause>
    [transition]

  rule <k> L':Term => Ls ...</k>
       <fresh>  L:Term :- Ls:Terms. => . </fresh>
       <mgu> Theta:Mgu => updateMgu(Theta,L,L') </mgu>

endmodule
