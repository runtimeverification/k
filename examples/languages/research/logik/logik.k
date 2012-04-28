require /modules/unification

module LOGIK-SYNTAX
  syntax Literal ::=  Id 
                   | Id "(" Literals ")" [prec 0]
  syntax Literals ::= List{Literal,","} [prec 60]

  syntax Clause ::=  Literal ";"  [prec 80]
                  | Literal ":-" Literals ";" [prec 70]
  syntax Query ::= "?-" Literals ";" [prec 70]
  syntax Pgm ::= Clause Pgm [prec 90]
               | Query

  macro X:Id,Lits:Literals = X(),Lits
  macro Lit:Literal; = Lit :-;
  macro X:Id :- Lits:Literals; = X() :- Lits;

end module

module LOGIK-SEMANTICS
  imports LOGIK-SYNTAX
  imports UNIFICATION

 configuration
   <T>
    <substitution> .K </substitution>
    <clauses>
          .Bag
    </clauses>
    <k>
      $PGM:K
    </k>
    <nextVar> 0 </nextVar>
   </T>
   <solution multiplicity="?"> .K </solution>

  syntax Id ::= UnificationVar

//@ Defining as unification variables all Ids starting with a small letter
  define 'isUnificationVar(K) => true when asciiString(substrString(Id2String(K),0,1)) <Int 96

//@ Final rule for extracting the solution
  rule <T>... <substitution> K:K </substitution> <k> .Literals </k> ...</T>
    => <solution> K </solution>

//@ Find a clause with the same name and generate a fresh version of it
  rule <k> (.K => alpha(Clause)) 
          ~> (_`(_`)(X:Id,ArgsKs:Literals),_:Literals) </k> 
      <clauses>... BagItem(Clause) ...</clauses>
  where Clause = _`(_`)(X,Params:Literals) :- Body:Literals;
  [transition]


/*@ Unify the goal with the clause head and replace the goal with the clause body.
*/
  rule Lit:Literal :- Lits:Literals; ~> Lit':Literal,Lits':Literals
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
  where Clause =  _`(_`)(X:Id,Params:Literals) :- Body:Literals;

/*@ To preserve the variables in the query we generate a substitution mapping 
them to fresh variables, then we save this substitution as the current solution,
while applying it on the Literals to ensure the query variables appear only in
the solution.
*/
  syntax K ::= initSolution

  rule <k> ?- Lits:Literals; 
        => getAlpha(Lits) ~> initSolution ~> applyAlpha(Lits) </k>

  rule <k> subst(Eqns:List{K}) ~> (initSolution => .K) ...</k>
       <substitution> .K => subst(Eqns) </substitution>
end module
