require "builtins/bool.k"
require "builtins/k-equal.k"
require "builtins/symbolic-k.k"
module UNIFICATION
  imports SYMBOLIC-K
  imports BOOL-HOOKS
  imports K-EQUAL-HOOKS

//@ Public interface to the unification procedure (what the user needs to know)
  syntax Mgu ::= ".Mgu"
  rule .Mgu => subst(.List{K})  [structural, anywhere]  // empty mgu
  rule isMgu(subst(_)) => true  [function]  // so we can write Theta:Mgu

  syntax Mgu ::= updateMgu(Mgu,K,K)  [function]  // updates Mgu with equation
  syntax K ::= applyMgu(Mgu,K)       [function, latex({#1}({#2}))]  // applies Mgu to any term
  rule applyMgu(Theta:Mgu,K) => applySubst(Theta,K)

  syntax Set ::= applyMgu(Mgu,Set)  [function, latex({#1}({#2}))]
  rule applyMgu(_, .Set) => .Set
  rule applyMgu(Theta:Mgu, SetItem(K:K) S:Set)
    => SetItem(applyMgu(Theta,K)) applyMgu(Theta,S)
// Traian: I would remove applySubst all together and only keep applyMgu
//         Mgu gives a nicer, more intuitive user interface than Subst

//@ Cleanup, decomposition and orientation of equations.

  rule eqns((eqn(K:K,,K) => .List{K}),,_)   [structural, anywhere]

/*@ Generic rule for decomposing the constraints.  
Matching on any KAST label, the 
*/ 
  rule eqns((.List{K} => eqn(K1,,K2)),, 
            eqn(L:KLabel((K1:K => .List{K}),,Ks:List{K}),,
                L((K2:K => .List{K}),,Ks':List{K})),,_)
    when (isVariable(L(K1,,Ks)) =/=K true)
         andBool (isVariable(L(K2,,Ks')) =/=K true)
    [structural, anywhere]
  rule eqns((eqn(K:K,,X:Variable) => eqn(X,,K)),,_)
    when isVariable(K) =/=K true   [structural, anywhere]


  rule unifyEqs(subst(_:List{K}),,eqns( 
            eqn(L1:KLabel(Ks:List{K}),,
                L2:KLabel(Ks':List{K})),,_))
    => clash(L1:KLabel(Ks:List{K}),,
                L2:KLabel(Ks':List{K}))
    when (isVariable(L1(Ks)) =/=K true)
         andBool (isVariable(L2(Ks')) =/=K true)
         andBool L1 =/=KLabel L2
    [structural, anywhere]


/*@ When an equation contains a variable, it can be added as a binding
to the mgu.  While we know that the variables in the domain of the mgu
do not appear anywhere in the equations, it can be and usually is the
case that variables appearing in the equations also appear in the
codomain of the mgu.  Thus, we have to refine the mgu by applying the
new binding to all its terms.  Moreover, to maintain the equations
canonical in terms of the current mgu, we also have to refine the
remaining equations by applying the new mgu binding to them. */


  rule unifyEqs(subst(Ks:List{K} => eqn(X,,K),,substitute(X,,K,,Ks)),,
              (eqns(eqn(X:Variable,,K:K),,Eqns:List{K})
               => substitute(X,, K,, eqns(Eqns))))
    when notBool(X subTerm K)
   [structural, anywhere]

  rule unifyEqs(subst(_),,eqns(eqn(X:Variable,,K:K),,_))
    => cycle(X,,K)
    when X subTerm K [anywhere]

/*@ Final rule of the unification algorithm, retrieving the substitution 
once all constraints were incorporated.
*/
  rule unifyEqs(subst(Eqns:List{K}),,eqns(.List{K})) => subst(Eqns)
   [structural, anywhere]
/*@ the subTerm relation is used to determine cyclic uunification */
  syntax Bool ::= K "subTerm" K [function]
  rule K1 subTerm K2 => (K1 ==K K2) orElseBool (K1 properSubTerm K2)
    [structural, anywhere]
  syntax Bool ::= K "properSubTerm" K [function]
  rule K1 properSubTerm L:KLabel(.List{K}) => false   [structural, anywhere]
  rule K1:K properSubTerm L:KLabel(K2:K,,Ks:List{K}) 
      => (K1 subTerm K2) orElseBool (K1 properSubTerm L:KLabel(Ks))
   [structural, anywhere]
/*@ Generic first order substitution on K ASTs.  
Note that ~> is not handled  and neither are binding operations.
*/

  rule substitute(X:K,,K:K,,.List{K}) => .List{K}   [structural, anywhere]
  rule substitute(X:K,,K:K,,K1:K,,K2:K,,Ks:List{K})
    => substitute(X,,K,,K1),,substitute(X,,K,,K2),,substitute(X,,K,,Ks) 
    [structural, anywhere]
  rule substitute(X:K,,K:K,,X) => K   [structural, anywhere]
  rule substitute(X:K,,K:K,,L:KLabel(Ks:List{K}))
    => L:KLabel(substitute(X,,K,,Ks))
    when X =/=K L:KLabel(Ks)
   [structural, anywhere]

  syntax K ::= "unify" "(" K "," K ")" [function]
  rule unify(K1, K2) => unifyEqs(subst(.List{K}),,eqns(eqn(K1,,K2))) 
   [structural, anywhere]
/*@ updateMgu adds a constraint cu the current MGU substitution.
The existing mgu is first applied to the constraint being introduced to 
guarantee that the variables in the domain of the mgu don't appear in the 
constraint.
*/

  rule updateMgu(subst(Ks:List{K}), K1, K2)
      => unifyEqs(subst(Ks),,eqns(applySubst(subst(Ks),eqn(K1,,K2))))
   [structural, anywhere]
  syntax K ::= applySubst(K, K) [function]
  rule applySubst(subst((eqn(K1:K,,K2:K) => .List{K}),,_),
                    (K:K => substitute(K1,, K2,, K)))   [structural, anywhere]
  rule applySubst(subst(.List{K}),K) => K   [structural, anywhere]
  
  syntax KLabel ::= "unifyEqs" | "subst" | "#vars" | "substitute"
                  | "eqn" | "eqns" | "mgu"
                  | "getVars" | "accumulateVars"
                  | "clash" | "cycle"

  syntax MguError ::= "dummy-used-only-for-declaration-purposes"
  rule isMguError(clash(_)) => true
  rule isMguError(cycle(_)) => true

  rule getVars(K) => accumulateVars(#vars(.List{K}),, K)
    [structural, anywhere]

  rule accumulateVars(#vars(Xs:List{K}),,X:Variable,,Ks:List{K}) 
    => #if (X inList{K} Xs)
       #then accumulateVars(#vars(Xs),,Ks)
       #else accumulateVars(#vars(Xs,,X),,Ks)
       #fi
    [structural, anywhere]
  rule accumulateVars(_:K,,(L:KLabel(Ks:List{K}) => Ks),,_)
    when isVariable(L(Ks)) =/=K true
    [structural, anywhere]
  rule accumulateVars(#vars(Xs:List{K})) => #vars(Xs)   [structural, anywhere]


//  configuration <k> .K </k> <nextVar> 0 </nextVar>

  syntax K ::= getAlpha(K)  [function]
  rule getAlpha(K)
    => freshSubst(subst(.List{K}),, getVars(K))

  syntax K ::= freshSubst(List{K})  [function]

  rule freshSubst(subst(_,,(.List{K} => 
                  eqn(X:K,,#freshSym(X)))),,
                  #vars((X => .List{K}),,_))
  rule freshSubst(subst(Eqns:List{K}),,#vars(.List{K})) => subst(Eqns)

// alpha conversion moved here by grigore
 syntax K ::= renameVariables(K)  [function]
            | applyAlpha(K)

// rule renameVariables(K) => getAlpha(K) ~> applyAlpha(K)
// rule subst(Eqns:List{K}) ~> applyAlpha(K) => applySubst(subst(Eqns),K)
 rule renameVariables(K) => applySubst(getAlpha(K),K)

// Turns an Mgu into a Map, ignoring the symbolic bindings
  syntax Map ::= Mgu2Map(K) [function]

  rule Mgu2Map(subst((eqn(K1:K,,_:K) => .List{K}),,_))
    when isSymbolicK(K1)   // ignore symbolic bindings
  rule Mgu2Map(subst((eqn(K1:K,,K2:K) => .List{K}),,_))
       (. => K1 |-> K2)
    when isSymbolicK(K1) =/=K true

  rule Mgu2Map(subst(.List{K})) => .Map
endmodule

