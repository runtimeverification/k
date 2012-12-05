require "modules/unification.k"

module LOGIK-SYNTAX
  syntax Literal ::=  Id
                   | Id "(" Literals ")"
                   > "[" Literals "]"
                   | "[" Literals "|" Literal "]"
  syntax Literals ::= List{Literal,","}

  syntax Clause ::= Literal ":-" Literals "."
                  > Literal "."
  syntax Query ::= "?-" Literals "."
  syntax Pgm ::= Query
               > Clause Pgm
endmodule

module LOGIK-SEMANTICS
  imports LOGIK-SYNTAX
  imports UNIFICATION

  configuration <T multiplicity="?">
                  <k> $PGM:K </k>
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
  
//@ Normalizing the definition.
  rule L:Literal. => L :- .Literals .                                [macro]
  rule X:Id :- Ls:Literals. => X(.Literals) :- Ls.                   [macro]
  rule [L:Literal, Ls] => [L | [Ls]]                                 [macro]
  rule [L:Literal, Ls | T] => [L|[Ls|T]]  when Ls =/=K .Literals     [macro]
  rule X:Id, Ls => X(.Literals), Ls  when isVariable(X) =/=K true    [macro]

//@ Sequentialize goals
  rule L:Literal, Ls:Literals => L ~> Ls
  rule .Literals => .

//@ Find a clause with the same name and generate a fresh version of it
  rule <k> (.K => renameVariables(X(Params:Literals) :- Body:Literals.))
          ~> X:Id(Args:Literals) ...</k>
       <clause> X(Params:Literals) :- Body:Literals. </clause>
    [transition]

/*@ Unify the goal with the clause head and replace the goal with the
clause body.  */
  rule <k> (L:Literal :- Ls:Literals.) ~> L':Literal => Ls ...</k>
       <mgu> Theta:Mgu => updateMgu(Theta,L,L') </mgu>

endmodule

module LOGIK
  imports LOGIK-SEMANTICS
//@ Add clauses to the set of clauses
  rule <k> ((X:Id(Params:Literals)) :- Body:Literals.) Pgm:K => Pgm </k>
       (. => <clause> X:Id(Params:Literals) :- Body:Literals. </clause>)

//@ when done processing clauses, simply "execute" the query.
  rule ?- Ls:Literals. => Ls

//@ Final rule for extracting the solution
  rule <T>... <k> . </k> <mgu> Theta:Mgu </mgu> ...</T> 
       <freshCounter> _ </freshCounter>
    => <solution> MGU2Solution(Theta) </solution>

//@ Rule for collapsing all error configurations into .
  rule <T>... <mgu> _:UnificationError </mgu> ...</T> 
       <freshCounter> _ </freshCounter>
     => .
endmodule
