require "modules/unification.k"

module LOGIK
  imports UNIFICATION

  syntax Literal ::= Id | Id "(" Literals ")"
  syntax Literals ::= List{Literal,","}
  syntax Clause ::= Literal ":-" Literals "." | Literal "."
  syntax Query ::= "?-" Literals "."
  syntax Pgm ::= Query | Clause Pgm

  configuration <T multiplicity="?">
                  <k> $PGM:Pgm </k>
                  <clauses>
                    <clause multiplicity="*"> .K </clause>
                  </clauses>
                  <mgu> .Mgu </mgu>
                </T>
                <solution multiplicity="?"> .Map </solution>

//@ Extend the syntax of Literals with (anonymous) variables
  syntax Literal ::= Variable

//@ Defining as unification variables all Ids starting with a capital letter
  rule isVariable(X:Id) => true
    when asciiString(substrString(Id2String(X),0,1)) <Int 96

//@ Sequentialize goals
  rule L:Literal, Ls:Literals => L ~> Ls
  rule .Literals => .

//@ Normalizing the definition.
  rule L:Literal. => L :- .Literals .                                [macro]
  rule X:Id :- Ls:Literals. => X(.Literals) :- Ls.                   [macro]
  rule X:Id, Ls => X(.Literals), Ls  when isVariable(X) =/=K true    [macro]

//@ Find a clause with the same name and generate a fresh version of it

//  rule <k> (.K => renameVariables(X(Params:Literals) :- Body:Literals.))
//          ~> X:Id(Args:Literals) ...</k>
//       <clause> X(Params:Literals) :- Body:Literals. </clause>
//    [transition]

  rule <k> . => renameVariables(C) ...</k>  <clause> C </clause>
    [transition]

/*@ Unify the goal with the clause head and replace the goal with the
clause body.  */
  rule <k> (L:Literal :- Ls:Literals.) ~> L':Literal => Ls ...</k>
       <mgu> Theta:Mgu => updateMgu(Theta,L,L') </mgu>


//@ Add clauses to the set of clauses
  rule <k> ((X:Id(Params:Literals)) :- Body:Literals.) Pgm:K => Pgm </k>
       (. => <clause> X:Id(Params:Literals) :- Body:Literals. </clause>)

//@ When done processing clauses, simply "execute" the query.
  rule ?- Ls:Literals. => Ls

//@ Final rule for extracting the solution
  rule <T>... <k> . </k> <mgu> Theta:Mgu </mgu> ...</T>
       <freshCounter> _ </freshCounter>
    => <solution> Mgu2Map(Theta) </solution>

//@ Rule for collapsing all error configurations into .Bag
  rule <T>... <mgu> _:MguError </mgu> ...</T>
       <freshCounter> _ </freshCounter>
    => .
endmodule
