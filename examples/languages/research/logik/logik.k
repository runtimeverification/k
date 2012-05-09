require /modules/unification

module LOGIK-SYNTAX
  syntax Literal ::=  Id 
                   | Id "(" Literals ")" [prec 0]
                   | "[" Literals "]"
                   | "[" Literals "|" Literal "]"
  syntax Literals ::= List{Literal,","} [prec 60]

  syntax Clause ::=  Literal "."  [prec 80]
                  | Literal ":-" Literals "." [prec 70]
  syntax Query ::= "?-" Literals "." [prec 70]
  syntax Pgm ::= Clause Pgm [prec 90]
               | Query

/*@ Normalizing the definition. 
Almost complete --- See additional rule in the semantics module. */
  macro Lit:Literal. = Lit :-.
  macro X:Id :- Lits:Literals. = X() :- Lits.

  macro [.Literals | L:Literal ] = L
  macro [L:Literal,Lits:Literals] = [L | [Lits]]
  macro [L1:Literal,L2:Literal,Lits:Literals|L':Literal]
      = [L1|[L2|[Lits|L']]]

end module

module LOGIK-SEMANTICS
  imports LOGIK-SYNTAX
  imports UNIFICATION

 configuration
   <T multiplicity="?">
    <substitution> .K </substitution>
    <clauses>
          .Bag
    </clauses>
    <k>
      $PGM:K
    </k>
    <nextVar> 0 </nextVar>
   </T>
   <solution stream="stdout"> .List </solution>

  syntax Id ::= UnificationVar


//@ Defining as unification variables all Ids starting with a small letter
  define 'isUnificationVar(K:K) => true when asciiString(substrString(Id2String(K),0,1)) <Int 96

//@ Normalizing all ids which are not used for unification
  rule X:Id,Lits:Literals => X(),Lits 
  when 'isUnificationVar(X) =/=K true
  [anywhere]

//@ Find a clause with the same name and generate a fresh version of it
  rule <k> (.K => alpha(Clause)) 
          ~> (_`(_`)(X:Id,Args:Literals),_:Literals) </k> 
      <clauses>... BagItem(Clause) ...</clauses>
  where Clause = _`(_`)(X,Params:Literals) :- Body:Literals.
  [transition]


/*@ Unify the goal with the clause head and replace the goal with the clause body.  */
  rule Lit:Literal :- Lits:Literals. ~> Lit':Literal,Lits':Literals
    => unify(Lit,Lit') ~> Lits @ Lits'

//@ if the unification succeeded, apply the mgu to the goals and the solution.
  rule <k> subst(Eqns:List{K}) ~> Lits:Literals 
        => applySubst(subst(Eqns),Lits) </k> 
       <substitution> K':K => applySubst(subst(Eqns),K') </substitution>


 syntax K ::= "alpha" "(" K ")" | "applyAlpha" "(" K ")"
 
 rule alpha(K) => getAlpha(K) ~> applyAlpha(K)
 rule subst(Eqns:List{K}) ~> applyAlpha(K) => applySubst(subst(Eqns),K)

//@ helping function:  append on literals
  syntax K ::= K "@" K [function prec 70]
  define Lit:Literal,Lits:Literals @ Lits':Literals 
      => Lit,(Lits @ Lits')
  define .Literals @ Lits:Literals  => Lits
end module

module LOGIK
  imports LOGIK-SEMANTICS
//@ Initialization

//@ Add clauses to the set of clauses
  rule <k> Clause Pgm:K => Pgm </k>
       <clauses>... . => BagItem(Clause) ...</clauses>
  where Clause =  _`(_`)(X:Id,Params:Literals) :- Body:Literals.

/*@ To preserve the variables in the query we generate a substitution mapping 
them to fresh variables, then we save this substitution as the current solution,
while applying it on the Literals to ensure the query variables appear only in
the solution.
*/
  syntax K ::= initSolution

  rule <k> ?- Lits:Literals. 
        => getAlpha(Lits) ~> initSolution ~> applyAlpha(Lits) </k>

  rule <k> subst(Eqns:List{K}) ~> (initSolution => .K) ...</k>
       <substitution> .K => subst(Eqns) </substitution>

/*@ printing the solution and disolving the rest. */

//@ Final rule for extracting the solution
  rule <substitution> K:K </substitution> <k> .Literals => print(K) </k>

  rule <T>... <k> .K </k> ...</T> => .

   syntax K ::= "print" "(" K ")" | "printStr" "(" String ")" | "printEqn" "(" K ")" | "printLit" "(" K ")" | "printLits" "(" K ")" | "printList" "(" K ")"

  rule print(subst(K,,Eqns:List{K}))
    => printEqn(K) ~> print(subst(Eqns))
  rule print(subst(.List{K})) => .

  rule printEqn(eqn(X:Id,,Lit:Literal)) => printStr(Id2String(X)) ~> printStr(" |-> ") ~> printLit(Lit) ~> printStr(";  ")


  rule printLit(X:Id) => printStr(Id2String(X))
  rule printLit(X:Id()) => printStr(Id2String(X)) 
  rule printLit(_`(_`)(X:Id,(Lit:Literal,Lits:Literals))) 
    => printStr(Id2String(X)) ~> printStr("(") ~> printLits(Lit,Lits) ~> printStr(")") 
  rule printLits(Lit:Literal,Lit':Literal,Lits:Literals) 
    => printLit(Lit) ~> printStr(", ") ~> printLits(Lit',Lits)
  rule printLits(Lit:Literal,.Literals) => printLit(Lit)

  rule <k> printStr(Str:String) => . ...</k>
      <solution>... . => ListItem(Str) </solution>

  rule printLit([]) => printStr("[]")
  rule printLit([Lit:Literal|Lit':Literal])
    => printStr("[") ~> printList([Lit:Literal|Lit':Literal]) ~> printStr("]")

  rule printList([Lit:Literal|[]]) => printLit(Lit)
  rule printList([Lit1:Literal|[Lit2:Literal|Lit':Literal]])
    => printLit(Lit1) ~> printStr(", ") ~> printList([Lit2|Lit'])

  rule printList([Lit:Literal|Lit':Literal])
    => printLit(Lit) ~> printStr(" | ") ~> printLit(Lit')
  when Lit' =/=K [.Literals]

  

  define Id2String(freshVar(N:Int)) => "_" +String Int2String(N)
end module
