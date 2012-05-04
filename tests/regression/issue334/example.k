module LOGIK-SYNTAX
  syntax Literal ::=  Id 
  syntax Literals ::= List{Literal,","}

  syntax Literal ::= Id "(" Literals ")"
  syntax Clause ::=  Literal "."
  syntax Clause ::= Literal ":-" Literals "." 
/*
  syntax Query ::= "?-" Literals "."
  syntax Pgm ::= Query 
*/
  syntax Pgm ::= Clause Pgm
end module

module LOGIK
  imports LOGIK-SYNTAX
 configuration
   <T>
    <substitution> .K </substitution>
    <clauses>
          .Map
    </clauses>
    <k>
      $PGM:K
    </k>
    <nextVar> 0 </nextVar>
   </T>
   <solution multiplicity="?"> .K </solution>

end module 

/*

module LOGIK
  imports UNIFICATION

  syntax K ::= K :- K 

  configuration
   <T>
    <substitution> .K </substitution>
    <clauses>
          .Map
    </clauses>
    <k>
      $PGM:K
    </k>
    <nextVar> 0 </nextVar>
   </T>
   <solution multiplicity="?"> .K </solution>

  rule <T>... <substitution> K:K </substitution> <k> .K </k> ...</T>
    => <solution> K </solution>

  rule <k> (.K => freshClause(L(Ks') :- literals(Lits)) ~> unifyWith(L(Ks))) 
           ~> goals((L:KLabel(Ks:List{K}) => .List{K}),,_) </k> 
      <clauses> L(Ks':List{K}) |-> literals(Lits:List{K}) </clauses>
  [transition]

  rule freshClause(K) 
    => freshSubst(subst(.List{K}),, getVars(K)) ~> makeFresh(K)

  syntax KLabel ::= "freshSubst" | "freshClause" | "makeFresh" | "unifyWith" 
                  | "concretize" | "goals" | "literals"
  

  rule <k> freshSubst(subst(_,,(.List{K} => eqn(X:K,,freshVar(N)))),,(X => .List{K}),,_) ...</k> <nextVar> N:Int => N +Int 1 </nextVar>

  rule freshSubst(subst(Eqns:List{K})) ~> makeFresh(K) 
    => applySubst(subst(Eqns), K)

  rule K1:K :- K ~> unifyWith(K2:K) => unify(K1, K2) ~> concretize(K)
  rule <k> subst(Eqns:List{K}) ~> concretize(K) => applySubst(subst(Eqns),K) 
       ...</k> 
       <substitution> K':K => applySubst(subst(Eqns),K') </substitution>

  rule (literals(Lits:List{K}) => .K) ~> goals((.List{K} => Lits),,_)
  
end module

*/
