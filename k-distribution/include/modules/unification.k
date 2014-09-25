// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "builtins/bool.k"
require "builtins/k-equal.k"
require "builtins/symbolic-k.k"
module UNIFICATION
  imports SYMBOLIC-K
  imports BOOL-HOOKS
  imports K-EQUAL-HOOKS

//@ Public interface to the unification procedure (what the user needs to know)
  syntax Mgu ::= ".Mgu"  [constructor, hook(Unification:emptyMgu)]
  rule .Mgu => subst(.KList)  [structural, anywhere]  // empty mgu
  rule isMgu(subst(_)) => true  [function]  // so we can write Theta:Mgu

  syntax Mgu ::= updateMgu(Mgu,K,K)  [function, hook(Unification:updateMgu)]  // updates Mgu with equation
  syntax K ::= applyMgu(Mgu,K)       [function, hook(Unification:applyMgu), latex({#1}({#2}))]  // applies Mgu to any term
  rule applyMgu(Theta:Mgu,K) => applySubst(Theta,K)

//  syntax Set ::= applyMgu(Mgu,Set)  [function, latex({#1}({#2}))]
  rule applyMgu(_, .Set) => .Set
  rule applyMgu(Theta:Mgu, SetItem(K:K) S:Set)
    => SetItem(applyMgu(Theta,K)) applyMgu(Theta,S)

/* If the user's language supports unification against don't-care terms
    (e.g. _ in Prolog), they should declare some syntax like the following:
syntax ThingThatCanBeUnified ::= "_" [onlyLabel, klabel($dontcare)]
*/
  syntax KItem ::= "$dontcare" [klabel($dontcare), latex(\AnyVar[K])]

// Traian: I would remove applySubst all together and only keep applyMgu
//         Mgu gives a nicer, more intuitive user interface than Subst

//@ Cleanup, decomposition and orientation of equations.

  rule eqns((eqn(K:K,,K) => .KList),,_)   [structural, anywhere]

/*@ Generic rule for decomposing the constraints.
Matching on any KAST label, the
*/
  rule eqns((.KList => eqn(K1,,K2)),,
            eqn(L:KLabel((K1:K => .KList),,Ks:KList),,
                L((K2:K => .KList),,Ks':KList)),,_)
    when (isVariable(L(K1,,Ks)) =/=K true)
         andBool (isVariable(L(K2,,Ks')) =/=K true)
         andBool (L(K1) =/=K $dontcare)
         andBool (L(K2) =/=K $dontcare)
    [structural, anywhere]
  rule eqns((eqn(K:K,,$dontcare) => .KList),,_) [structural, anywhere]
  rule eqns((eqn($dontcare,,K:K) => .KList),,_) [structural, anywhere]
  rule eqns((eqn(K:K,,X:Variable) => eqn(X,,K)),,_)
    when isVariable(K) =/=K true   [structural, anywhere]


  rule unifyEqs(subst(_:KList),,eqns(
            eqn(L1:KLabel(Ks:KList),,
                L2:KLabel(Ks':KList)),,_))
    => clash(L1:KLabel(Ks:KList),,
                L2:KLabel(Ks':KList))
    when (isVariable(L1(Ks)) =/=K true)
         andBool (L1(Ks ) =/=K $dontcare)
         andBool (isVariable(L2(Ks')) =/=K true)
         andBool (L2(Ks') =/=K $dontcare)
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


  rule unifyEqs(subst(Ks:KList => eqn(X,,K),,substitute(X,,K,,Ks)),,
              (eqns(eqn(X:Variable,,K:K),,Eqns:KList)
               => substitute(X,, K,, eqns(Eqns))))
    when notBool(X subTerm K)
   [structural, anywhere]

  rule unifyEqs(subst(_),,eqns(eqn(X:Variable,,K:K),,_))
    => cycle(X,,K)
    when X subTerm K [anywhere]

/*@ Final rule of the unification algorithm, retrieving the substitution
once all constraints were incorporated.
*/
  rule unifyEqs(subst(Eqns:KList),,eqns(.KList)) => subst(Eqns)
   [structural, anywhere]
/*@ the subTerm relation is used to determine cyclic uunification */
  syntax Bool ::= K "subTerm" K [function]
  rule K1 subTerm K2 => (K1 ==K K2) orElseBool (K1 properSubTerm K2)
    [structural, anywhere]
  syntax Bool ::= K "properSubTerm" K [function]
  rule K1 properSubTerm L:KLabel(.KList) => false   [structural, anywhere]
  rule K1:K properSubTerm L:KLabel(K2:K,,Ks:KList)
      => (K1 subTerm K2) orElseBool (K1 properSubTerm L:KLabel(Ks))
   [structural, anywhere]
/*@ Generic first order substitution on K ASTs.
Note that ~> is not handled  and neither are binding operations.
*/

  rule substitute(X:K,,K:K,,.KList) => .KList   [structural, anywhere]
  rule substitute(X:K,,K:K,,K1:K,,K2:K,,Ks:KList)
    => substitute(X,,K,,K1),,substitute(X,,K,,K2),,substitute(X,,K,,Ks)
    [structural, anywhere]
  rule substitute(X:K,,K:K,,X) => K   [structural, anywhere]
  rule substitute(X:K,,K:K,,L:KLabel(Ks:KList))
    => L:KLabel(substitute(X,,K,,Ks))
    when X =/=K L:KLabel(Ks)
     andBool (isCollection(L(Ks)) =/=K true)
   [structural, anywhere]

  //TODO:  Consider implementing substitute for other collections, too
  rule substitute(X:K,, K:K,, L:List,,Ks:KList)
    => substituteList(X, K, L),, substitute(X,, K,, Ks)
  rule substitute(X:K,, K:K,, S:Set,,Ks:KList)
    => substituteSet(X, K, S),, substitute(X,, K,, Ks)

  syntax Set ::= substituteSet(K,K,Set) [function]
  rule substituteSet(X:K, K:K, .Set) => .Set
  rule substituteSet(X:K, K:K, SetItem(K1:K) S:Set)
    => SetItem(substitute(X,,K,, K1)) substituteSet(X,K,S)

  syntax List ::= substituteList(K,K,List) [function]
  rule substituteList(X:K, K:K, .List) => .List
  rule substituteList(X:K, K:K, ListItem(K1:K) L:List)
    => ListItem(substitute(X,,K,, K1)) substituteList(X,K,L)

  syntax K ::= "unify" "(" K "," K ")" [function]
  rule unify(K1, K2) => unifyEqs(subst(.KList),,eqns(eqn(K1,,K2)))
   [structural, anywhere]
/*@ updateMgu adds a constraint cu the current MGU substitution.
The existing mgu is first applied to the constraint being introduced to
guarantee that the variables in the domain of the mgu don't appear in the
constraint.
*/

  rule updateMgu(subst(Ks:KList), K1, K2)
      => unifyEqs(subst(Ks),,eqns(applySubst(subst(Ks),eqn(K1,,K2))))
   [structural, anywhere]
  syntax K ::= applySubst(K, K) [function]
  rule applySubst(subst((eqn(K1:K,,K2:K) => .KList),,_),
                    (K:K => substitute(K1,, K2,, K)))   [structural, anywhere]
  rule applySubst(subst(.KList),K) => K   [structural, anywhere]

  syntax KLabel ::= "unifyEqs" | "subst" | "#vars" | "substitute"
                  | "eqn" | "eqns" | "mgu"
                  | "getVars" | "accumulateVars"
                  | "clash" | "cycle"

  syntax MguError
  syntax MguOrError ::= Mgu | MguError
  rule isMguError(clash(_)) => true
  rule isMguError(cycle(_)) => true

  rule getVars(K) => accumulateVars(#vars(.KList),, K)
    [structural, anywhere]

  rule accumulateVars(#vars(Xs:KList),,X:Variable,,Ks:KList)
    => #if (X inKList Xs)
       #then accumulateVars(#vars(Xs),,Ks)
       #else accumulateVars(#vars(Xs,,X),,Ks)
       #fi
    [structural, anywhere]
  rule accumulateVars(_:K,,(L:KLabel(Ks:KList) => Ks),,_)
    when isVariable(L(Ks)) =/=K true
    [structural, anywhere]
  rule accumulateVars(#vars(Xs:KList)) => #vars(Xs)   [structural, anywhere]


//  syntax Map ::= applyMgu(Mgu, Map) [function]
  rule applyMgu(Mgu, ((X |-> V) M:Map))
    => (X |-> applyMgu(Mgu,V)) applyMgu(Mgu, M)
  rule applyMgu(_,.Map) => .Map


  syntax Map ::= #metaVariablesMap(K) [function]
  rule #metaVariablesMap(K:K) => #metaVarsMap(getVars(K), .Map)

  syntax Map ::= #metaVarsMap(K, Map) [function]
  rule #metaVarsMap(#vars((X:K => .KList),,_),
       M:Map (.Map => #tokenToString(X) |-> X))
  rule #metaVarsMap(#vars(.KList), M:Map) => M:Map

//  configuration <k> .K </k> <nextVar> 0 </nextVar>

  syntax K ::= getAlpha(K)  [function]
  rule getAlpha(K)
    => freshSubst(subst(.KList),, getVars(K))

  syntax K ::= freshSubst(KList)  [function]

  rule freshSubst(subst(_,,(.KList =>
                  eqn(X:K,,#freshSym(X)))),,
                  #vars((X => .KList),,_))
  rule freshSubst(subst(Eqns:KList),,#vars(.KList)) => subst(Eqns)





// alpha conversion moved here by grigore
 syntax K ::= renameVariables(K)  [function, hook(MetaK:renameVariables)]
//            | applyAlpha(K)

// rule renameVariables(K) => getAlpha(K) ~> applyAlpha(K)
// rule subst(Eqns:KList) ~> applyAlpha(K) => applySubst(subst(Eqns),K)
 rule renameVariables(K) => applySubst(getAlpha(K),K)

// Turns an Mgu into a Map, ignoring the symbolic bindings
  syntax Map ::= Mgu2Map(K) [function]
  rule Mgu2Map(K) => Mgu2MapHelper(K, .Map)

  syntax Map ::= Mgu2MapHelper(K, Map) [function]

  rule Mgu2MapHelper(subst((eqn(K1:K,,_:K) => .KList),,_), _)
    when isSymbolicK(K1)   // ignore symbolic bindings
  rule Mgu2MapHelper(subst((eqn(K1:K,,K2:K) => .KList),,_), M:Map
       (.Map => K1 |-> K2))
    when isSymbolicK(K1) =/=K true

/*
  rule Mgu2Map(subst((eqn(K1:K,,K2:K) => eqn(K2:K,,K1:K)),,_))
    when isSymbolicK(K1)
    andBool isVariable(K2)
    andBool isSymbolicK(K2) =/=K true
// reorient symbolic-to-concrete variable bindings

  rule Mgu2Map(subst((eqn(K1:K,,K2:K) => .KList),,_))
    when isSymbolicK(K1)
    andBool isSymbolicK(K2)
  rule Mgu2Map(subst((eqn(K1:K,,K2:K) => .KList),,_))
    when isSymbolicK(K1)
    andBool (isVariable(K2) =/=K true)
  // ignore symbolic bindings
  rule Mgu2Map(subst((eqn(K1:K,,K2:K) => .KList),,_))
       (. => K1 |-> K2)
    when isSymbolicK(K1) =/=K true

*/


  rule Mgu2MapHelper(subst(.KList), M:Map) => M



endmodule
