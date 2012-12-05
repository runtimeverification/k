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
                <solution stream="stdout"> .List </solution>

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

//  rule (L:Literal :- Ls:Literals.) ~> (L':Literal,Ls':Literals)
//    => unify(L,L') ~> (Ls @ Ls')

//@ if the unification succeeded, apply the mgu to the goals and the solution.
//  rule <k> Theta:Mgu ~> Ls:Literals
//        => applyMgu(Theta,Ls) </k>
//       <mgu> K':K => applyMgu(Theta,K') </mgu>


//@ helping function:  append on literals
//  syntax K ::= K "@" K [function]
//  rule L:Literal,Ls:Literals @ Ls':Literals => L,(Ls @ Ls')
//  rule .Literals @ Ls:Literals  => Ls

endmodule

module LOGIK
  imports LOGIK-SEMANTICS
//@ Initialization

//@ Add clauses to the set of clauses
  rule <k> ((X:Id(Params:Literals)) :- Body:Literals.) Pgm:K => Pgm </k>
       (. => <clause> X:Id(Params:Literals) :- Body:Literals. </clause>)

/*@ To preserve the variables in the query we generate a substitution mapping
them to fresh variables, then we save this substitution as the current
solution, while applying it on the Literals to ensure the query variables
appear only in the solution. */
//  syntax K ::= "initSolution"

// why not just this instead?
  rule ?- Ls:Literals. => Ls

//  rule <k> ?- Ls:Literals.
//        => getAlpha(Ls) ~> initSolution ~> applyAlpha(Ls) </k>

//  rule <k> subst(Eqns:List{K}) ~> (initSolution => .K) ...</k>
//       <mgu> _ => subst(Eqns) </mgu>

/*@ printing the solution and disolving the rest. */

//@ Final rule for extracting the solution

  rule <T> <k> . => print(Theta) </k> (_ <mgu> Theta:Mgu </mgu> => .) </T>

  rule <T> <k> .K </k> </T> => .

   syntax K ::= print(K)
              | printStr(String)
              | printEqn(K)
              | printLit(K)
              | printLits(K)
              | printList(K)

  rule print(subst(K,,Eqns:List{K}))
    => printEqn(K) ~> print(subst(Eqns))
  rule print(subst(.List{K})) => .

  rule printEqn(eqn(X:Id,,L:Literal))
    => printStr(Id2String(X))
       ~> printStr(" |-> ") ~> printLit(L) ~> printStr(";  ")

// added by Grigore
  rule printEqn(eqn(#symVariable(_),,_)) => .

  rule printLit(#symVariable(N:Int)) => printStr("_" +String Int2String(N))
  rule printLit(X:Id) => printStr(Id2String(X))
  rule printLit(X:Id(.Literals)) => printStr(Id2String(X)) 
  rule printLit(X:Id(L:Literal,Ls:Literals)) 
    => printStr(Id2String(X))
       ~> printStr("(") ~> printLits(L,Ls) ~> printStr(")")
  rule printLits(L:Literal,L':Literal,Ls:Literals)
    => printLit(L) ~> printStr(", ") ~> printLits(L',Ls)
  rule printLits(L:Literal,.Literals) => printLit(L)

  rule <k> printStr(Str:String) => . ...</k>
       <solution>... . => ListItem(Str) </solution>

  rule printLit([.Literals]) => printStr("[]")
  rule printLit([L:Literal|L':Literal])
    => printStr("[") ~> printList([L:Literal|L':Literal]) ~> printStr("]")

  rule printList([L:Literal|[.Literals]]) => printLit(L)
  rule printList([L1:Literal|[L2:Literal|L':Literal]])
    => printLit(L1) ~> printStr(", ") ~> printList([L2|L'])

  rule printList([L:Literal|L':Literal])
    => printLit(L) ~> printStr(" | ") ~> printLit(L')
  when L' =/=K [.Literals]

endmodule
