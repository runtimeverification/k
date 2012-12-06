require "modules/unification.k"

module LOGIK
  imports UNIFICATION

  syntax Term ::= Id | Id "(" Terms ")"
  syntax Terms ::= List{Term,","}
  syntax Clause ::= Term ":-" Terms "." | Term "."
  syntax Query ::= "?-" Terms "."
  syntax Pgm ::= Query | Clause Pgm

  configuration <T multiplicity="?">
                  <k> $PGM:Pgm </k>
                  <clauses>
                    <clause multiplicity="*"> .K </clause>
                  </clauses>
                  <mgu> .Mgu </mgu>
                </T>
                <solution multiplicity="?"> .Map </solution>

//@ Extend the syntax of Terms with (anonymous) variables
  syntax Term ::= Variable

//@ Defining as unification variables all Ids starting with a capital letter
  syntax Variable ::= CapitalizedId

//@ Normalizing the definition.
  rule L. => L :- .Terms .                                       [macro]
// What I would really like to say here, but the tool does not allow us
// to do that yet, is:
//   rule IdAsTerm(X) => X(.Terms) when isCapitalizedId(X) =/= true  [macro]
// Instead, we currently have to add rules like the following
  rule (X:Id => X(.Terms)) :- _ .                                [macro]
  rule (X:Id => X(.Terms)),_  when isCapitalizedId(X) =/=K true  [macro]


//@ Add clauses to the set of clauses
  rule <k> ((X:Id(Params:Terms)) :- Body:Terms.) Pgm:K => Pgm </k>
       (. => <clause> X:Id(Params:Terms) :- Body:Terms. </clause>)

//@ When done processing clauses, simply "execute" the query.
  rule ?- Ls:Terms. => Ls

//@ Sequentialize goals
  rule L:Term, Ls:Terms => L ~> Ls
  rule .Terms => .


//@ Pick a clause and generate a fresh instance of it

  rule <k> . => renameVariables(C) ...</k>  <clause> C </clause>
    [transition]

/*@ Unify the goal with the clause head and replace the goal with the
clause body.  */
  rule <k> (L:Term :- Ls:Terms.) ~> L':Term => Ls ...</k>
       <mgu> Theta:Mgu => updateMgu(Theta,L,L') </mgu>


//@ Final rule for extracting the solution
  rule <T>... <k> . </k> <mgu> Theta:Mgu </mgu> ...</T>
       <freshCounter> _ </freshCounter>
    => <solution> Mgu2Map(Theta) </solution>

//@ Rule for collapsing all error configurations into .Bag
  rule <T>... <mgu> _:MguError </mgu> ...</T>
       <freshCounter> _ </freshCounter>
    => .
endmodule
