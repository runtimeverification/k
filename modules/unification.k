module UNIFICATION is

  syntax UnificationVar ::= "freshVar" "(" Int ")"

  define eqns((.List{K} => eqn(K1,,K2)),, 
            eqn(L:KLabel((K1:K => .List{K}),,Ks:List{K}),,
                L((K2:K => .List{K}),,Ks':List{K})),,_)
    when 'isUnificationVar(L(K1,,Ks)) =/=K true  
         andBool 'isUnificationVar(L(K2,,Ks')) =/=K true
 
  
  define eqns((eqn(K:K,,K) => .List{K}),,_)

  define eqns((eqn(K,,X:K) => eqn(X,,K)),,_) when 'isUnificationVar(X) andBool 'isUnificationVar(K) =/=K true

  define unifyEqs(subst(Ks:List{K} => eqn(X,,K),,substitute(X,,K,,Ks)),,
              (eqns(eqn(X,,K),,Eqns:List{K}) => substitute(X,, K,, eqns(Eqns))))
    when 'isUnificationVar(X) andBool notBool(X subTerm K)

  define unifyEqs(subst(Eqns:List{K}),,eqns(.List{K})) => subst(Eqns)

  syntax Bool ::= K "subTerm" K [function]
  syntax Bool ::= K "properSubTerm" K [function]
  
  define K1 subTerm K2 => K1 ==K K2 orElseBool K1 properSubTerm K2
  define K1 properSubTerm L:KLabel(.List{K}) => false
  define K1 properSubTerm L:KLabel(K2,,Ks:List{K}) 
      => K1 subTerm K2 orElseBool K1 properSubTerm L(Ks)


  define substitute(X,,K,,.List{K}) => .List{K}
  define substitute(X,,K,,K1,,K2,,Ks:List{K})
      => substitute(X,,K,,K1),,substitute(X,,K,,K2),,substitute(X,,K,,Ks)
  define substitute(X,,K,,X) => K
  define substitute(X,,K,,L(Ks:List{K})) => L(substitute(X,,K,,Ks))
    when X =/=K L(Ks)


  syntax K ::= "unify" "(" K "," K ")" [function]
  syntax K ::= "updateMgu" "(" K "," K "," K ")" [function]
  define unify(K1, K2) => unifyEqs(subst(.List{K}),,eqns(eqn(K1,,K2))) 
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
