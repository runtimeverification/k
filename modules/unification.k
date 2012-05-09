module UNIFICATION is

  syntax UnificationVar ::= "freshVar" "(" Int ")"

//@ Cleanup, decomposition and orientation of equations.

  define eqns((eqn(K:K,,K) => .List{K}),,_)

/*@ Generic rule for decomposing the constraints.  
Matching on any KAST label, the 
*/ 
  define eqns((.List{K} => eqn(K1,,K2)),, 
            eqn(L:KLabel((K1:K => .List{K}),,Ks:List{K}),,
                L((K2:K => .List{K}),,Ks':List{K})),,_)
    when 'isUnificationVar(L(K1,,Ks)) =/=K true  
         andBool 'isUnificationVar(L(K2,,Ks')) =/=K true
 
  define eqns((eqn(K,,X:K) => eqn(X,,K)),,_) when 'isUnificationVar(X) andBool 'isUnificationVar(K) =/=K true

/*@ When an equation contains a variable, it can be added as a binding
to the mgu.  While we know that the variables in the domain of the mgu
do not appear anywhere in the equations, it can be and usually is the
case that variables appearing in the equations also appear in the
codomain of the mgu.  Thus, we have to refine the mgu by applying the
new binding to all its terms.  Moreover, to maintain the equations
canonical in terms of the current mgu, we also have to refine the
remaining equations by applying the new mgu binding to them. */


  define unifyEqs(subst(Ks:List{K} => eqn(X,,K),,substitute(X,,K,,Ks)),,
              (eqns(eqn(X,,K),,Eqns:List{K}) => substitute(X,, K,, eqns(Eqns))))
    when 'isUnificationVar(X) andBool notBool(X subTerm K)

/*@ Final rule of the unification algorithm, retrieving the substitution 
once all constraints were incorporated.
*/
  define unifyEqs(subst(Eqns:List{K}),,eqns(.List{K})) => subst(Eqns)

/*@ the subTerm relation is used to determine cyclic uunification */
  syntax Bool ::= K "subTerm" K [function]
define K1 subTerm K2 => K1 ==K K2 orElseBool K1 properSubTerm K2

  syntax Bool ::= K "properSubTerm" K [function]
  define K1 properSubTerm L:KLabel(.List{K}) => false
  define K1 properSubTerm L:KLabel(K2,,Ks:List{K}) 
      => K1 subTerm K2 orElseBool K1 properSubTerm L(Ks)

/*@ Generic first order substitution on K ASTs.  
Note that ~> is not handled  and neither are binding operations.
*/

  define substitute(X,,K,,.List{K}) => .List{K}
  define substitute(X,,K,,K1,,K2,,Ks:List{K})
      => substitute(X,,K,,K1),,substitute(X,,K,,K2),,substitute(X,,K,,Ks)
  define substitute(X,,K,,X) => K
  define substitute(X,,K,,L(Ks:List{K})) => L(substitute(X,,K,,Ks))
    when X =/=K L(Ks)


  syntax K ::= "unify" "(" K "," K ")" [function]
  define unify(K1, K2) => unifyEqs(subst(.List{K}),,eqns(eqn(K1,,K2))) 

/*@ updateMgu adds a constraint cu the current MGU substitution.
The existing mgu is first applied to the constraint being introduced to 
guarantee that the variables in the domain of the mgu don't appear in the 
constraint.
*/
  syntax K ::= "updateMgu" "(" K "," K "," K ")" [function]
  define updateMgu(subst(Ks:List{K}), K1, K2)
      => unifyEqs(subst(Ks),,eqns(applySubst(subst(Ks),eqn(K1,,K2))))

  syntax K ::= "applySubst" "(" K "," K ")" [function]
  define applySubst(subst((eqn(K1,,K2) => .List{K}),,_), 
                    (K => substitute(K1,, K2,, K)))
  define applySubst(subst(.List{K}),K) => K
  
  syntax KLabel ::= "unifyEqs" | "subst" | "vars" | "substitute" 
                  | "eqn" | "eqns" | "mgu"
                  | "getVars" | "accumulateVars"

  define getVars(K) => accumulateVars(vars(.List{K}),, K)

  define accumulateVars(vars(Xs:List{K}),,X,,Ks:List{K}) 
     => #if (X inList{K} Xs)
        #then accumulateVars(vars(Xs),,Ks)
        #else accumulateVars(vars(Xs,,X),,Ks)
        #fi
     when 'isUnificationVar(X)

   define accumulateVars(_:K,,(L:KLabel(Ks:List{K}) => Ks),,_)
     when 'isUnificationVar(L(Ks)) =/=K true

   define accumulateVars(vars(Xs:List{K})) => vars(Xs)


   configuration <k> .K </k> <nextVar> 0 </nextVar>

   syntax K ::= "getAlpha" "(" K ")"
    rule getAlpha(K) 
    => freshSubst(subst(.List{K}),, getVars(K))

  syntax KLabel ::= "freshSubst" 

  rule <k> freshSubst(subst(_,,(.List{K} => eqn(X:K,,freshVar(N)))),,vars((X => .List{K}),,_)) ...</k> <nextVar> N:Int => N +Int 1 </nextVar>

  rule freshSubst(subst(Eqns:List{K}),,vars(.List{K})) => subst(Eqns)
end module
