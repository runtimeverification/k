require "pattern-matching.k"
require "builtins/symbolic-k.k"
require "k-prelude.k"

module VARIABLE
  imports SYMBOLIC-K
  imports K-FRESH

  syntax K ::= vars(Set)

  syntax Set ::= #getVarsFromK(K)  [function]
  rule #getVarsFromK(vars(Vars:Set)) => Vars

// Get the variables in a K term, going through the sets Klabeled as
// terms as well, if any.
// Grigore: We should also have a user-friendly variant of this, which
// returns an actual set of variables.  Well, I just added it, please check.

  syntax Set ::= getVariables(K)  [function]  // public
  rule getVariables(vars(Vars:Set)) => Vars

  syntax K ::= #getVars(K)  [function]
  rule #getVars(K:K) => #getVars1(K, .Set)

  syntax K ::= #getVars1(List{K}, Set)  [function]
  rule #getVars1((X:Variable => .List{K}),,_, _ (.Set => SetItem(X)))
  rule #getVars1(((Set2KLabel S:Set)(.List{K}) => Set2KTerm(S:Set)),,_, _)
  rule #getVars1((L:KLabel(Ks:List{K}) => Ks),,_, _)
    when isVariable(L(Ks)) =/=K true andBool isSet(L(Ks)) =/=K true
  rule #getVars1(.List{K}, S:Set) => vars(S)

// Generates a "fresh" local variable of the type of K that does not appear
// anywhere within the set Set
  syntax K ::= #freshVar(K, Set)  [function]
  rule #freshVar(L:KLabel(_), Ks:Set) => #freshVar1(Ks, L("local",,1))

  syntax K ::= #freshVar1(Set, K)  [function]
  rule #freshVar1(.Set, K:K) => K
  rule #freshVar1(SetItem(L:KLabel("local",,I1:Int)) Ks:Set,L("local",,I2:Int))
    => #if I1 >=Int I2 ==K true
       #then #freshVar1(Ks, L("local",, I1 +Int 1))
       #else #freshVar1(Ks, L("local",, I2))
       #fi
  rule #freshVar1((SetItem(K:K) => .Set) _, _)
    when isLocalFreshVar(K) =/=K true
//    when isSymbolicK(K) =/=K true
// Grigore: Traian, I do not understand why you had the condition above.
// It made some type inference examples fail.  See, for example,
// tutorial/5_types/lesson_4/tricky-1.lambda.  I think you meant "when K is a
// non-local variable.  I added the predicate below.

  syntax Bool ::= isLocalFreshVar(K)  [function]
  rule isLocalFreshVar(L:KLabel("local",,_:Int)) => true

endmodule


module BINDER
  imports VARIABLE
  syntax KLabel ::= "isBinder"

// Grigore: we should check why we get kompile errors when we
// remove the klabels below; they should be the default labels ...
  syntax Bool ::= isBound(KLabel, Int)  [klabel("isBound"), function]
  syntax Bool ::= isBounding(KLabel, Int) [klabel("isBounding"), function]

  syntax K ::= #splitedBinder(List{K}, List{K}, Set)

  syntax Bool ::= K "inVars" K  [function]
  rule K:K inVars vars(S:Set) => K in S

  syntax K ::= #boundVars(K)  [function]
  rule #boundVars(K:K) => #boundVars1(#binderSplit(K))

  syntax K ::= #boundVars1(K)  [function]
  rule #boundVars1(#splitedBinder(_, _, Bound:Set))
    => vars(Bound)

  syntax K ::= #binderSplit(K)  [function]
  rule #binderSplit(L:KLabel(Ks:List{K}))
    => #binderSplit1(L, 1, Ks, .List{K}, .List{K}, .Set)

  syntax K ::= #binderSplit1(KLabel,Int,List{K},List{K},List{K},Set)
    [function]
  rule #binderSplit1(L:KLabel, I:Int, K:K,,Ks:List{K},
                     NBEs:List{K}, BEs:List{K}, Bound:Set)
    => #if isBound(L,I) ==K true
       #then #binderSplit2(L, I +Int 1, Ks, NBEs, BEs, Bound, #getVars(K))
       #else #if isBounding(L, I) ==K true
             #then #binderSplit1(L, I +Int 1, Ks, NBEs, BEs,,K, Bound)
             #else #binderSplit1(L, I +Int 1, Ks, NBEs,,K, BEs, Bound)
             #fi
       #fi
  rule #binderSplit1(_, _, .List{K}, NBEs:List{K}, BEs:List{K}, Bound:Set)
    => #splitedBinder(NBEs, BEs, Bound)

// Grigore: remove this, once we change #getVars to return a set of variables
  syntax K ::= #binderSplit2(KLabel, Int, List{K}, List{K}, List{K}, Set, K)
    [function]
  rule #binderSplit2(L:KLabel, I:Int, Ks:List{K},
                     NBEs:List{K}, BEs:List{K}, Bound:Set, vars(Bound':Set))
    => #binderSplit1(L, I, Ks, NBEs, BEs, Bound Bound')

endmodule

module FREE-VARS
  imports BINDER

  syntax Set ::= freeVariables(List{K})  [function, latex({\it FV}({#1}))]  // public
               | freeVariables(Set)      [function, latex({\it FV}({#1}))]
  rule freeVariables(Ks:List{K}) => #getVarsFromK(#freeVars(Ks))
  rule freeVariables(.Set) => .Set
  rule freeVariables(SetItem(K) S:Set) => freeVariables(K) freeVariables(S)

// Grigore: again, I think this should just return a set of variables, not a K
// I added a user-interface variant of it above.  I use it in type-inference.
  syntax K ::= #freeVars(List{K})  [function]
  rule #freeVars(Ks:List{K}) => #freeVars(Ks:List{K}, .Set, .Set)

  syntax K ::= #freeVars(List{K}, Set, Set)  [function]
  rule #freeVars(.List{K}, _, Free:Set) => vars(Free)
  rule #freeVars(X:Variable,,Ks:List{K}, Bound:Set, Free:Set)
    => #if X in Bound ==K true #then #freeVars(Ks, Bound, Free)
       #else #freeVars(Ks, Bound, Free SetItem(X)) #fi
  rule #freeVars((Set2KLabel(S:Set)(.List{K}) => Set2KTerm(S)),,_, _, _)
  rule #freeVars((L:KLabel(Ks:List{K}) => Ks),, _, _, _)
    when (isVariable(L(Ks)) =/=K true) andBool
         (isBinder(L(Ks)) =/=K true) andBool
         (isSet(L(Ks)) =/=K true)
  rule #freeVars(K:K,,Ks:List{K}, Bound:Set, Free:Set)
    => #freeVars1(Ks, #freeVarsBinder(K, Bound), Bound, Free)
    when isBinder(K)

  syntax K ::= #freeVars1(List{K}, K, Set, Set)  [function]
  rule #freeVars1(Ks:List{K}, vars(Free1:Set), Bound:Set, Free2:Set)
    => #freeVars(Ks, Bound, Free1 Free2)

  syntax K ::= #freeVarsBinder(K, Set)  [function]
  rule #freeVarsBinder(K:K, Bound:Set)
    => #freeVarsBinder1(#binderSplit(K), Bound)

  syntax K ::= #freeVarsBinder1(K, Set)  [function]
  rule #freeVarsBinder1(
          #splitedBinder(NBEs:List{K}, BEs:List{K}, Bound1:Set), Bound:Set)
    => #freeVarsBinder2(
          #freeVars(NBEs, Bound, .Set), #freeVars(BEs, Bound1 Bound, .Set))

  syntax K ::= #freeVarsBinder2(K, K)  [function]
  rule #freeVarsBinder2(vars(Free1:Set), vars(Free2:Set)) => vars(Free1 Free2)
endmodule

module SUBSTITUTION
  imports FREE-VARS
  imports PATTERN-MATCHING

// Seems unnecessary
//  syntax K ::= #substitutionError(K,String)

// "Public" interface

  syntax K ::= K "[" List{K} "/" List{K} "]"  [function, prefer]
  syntax K ::= K "[" Map "]"  [function, prefer]

  rule K:K[Ks:List{K} / Vs:List{K}] => #substituteK(K,#patternMatch(Vs,Ks))
  rule K:K[M:Map] => #substitute(K, M)

//  rule _[_/V:K] 
//    => #substitutionError(V, "is not a Variable; cannot #substitute")
//    when isVariable(V) =/=K true

  syntax K ::= #substituteK(K, K)  [function]
             | #substitute(K, Map)  [function]
             | #substituteFV(K, Map, K)  [function]
             | #substituteList(K, Map, K)  [function]
             | #substituteList1(K, Map, K, List{K})  [function]

  rule #substituteK(K:K, #map(M:Map)) => #substitute(K,M)

// Grigore: should add Set ::= #freeVars(Set)
  rule #substitute(K:K, M:Map)
    => #substituteFV(K, M, #freeVars(Set2KLabel values(M)(.List{K})))

  rule #substituteFV(Y:Variable, M:Map, _)
    => #if $hasMapping(M, Y) #then M:Map(Y) #else Y #fi
  rule #substituteFV(K:K, M:Map, FV:K) => #substituteBinder(K, M, FV:K)
    when isBinder(K)
  rule #substituteFV(K:K, M:Map, FV:K) => #substituteList(K, M, FV)
    when isVariable(K) =/=K true andBool isBinder(K) =/=K true

  rule #substituteList(K:K,M:Map,FV:K) => #substituteList1(K,M,FV:K,.List{K})
  rule #substituteList1(_:KLabel((K:K => .List{K}),,_),M:Map,FV:K,
                        _,,(.List{K} => #substituteFV(K, M, FV)))
  rule #substituteList1(L:KLabel(.List{K}), _, _, Ks:List{K}) => L(Ks)

  syntax K ::= #substituteBinder(K, Map, K)  [function]
  rule #substituteBinder(K:K, M:Map, FV:K)
    => #substituteBinder1(K, M, #boundVars(K), FV)

  syntax K ::= #substituteBinder1(K, Map, K, K)  [function]
  rule #substituteBinder1(K:K, M:Map, vars(BKVs:Set), vars(FEVs:Set))
    => #substituteBinder2(K,M,vars(intersectSet(BKVs,FEVs keys M)),vars(FEVs))

  syntax K ::=  #substituteBinder2(K, Map, K, K)  [function]
  rule #substituteBinder2(K:K, M:Map, vars(Vs:Set), vars(FEVs:Set))
    => #if isEmptySet(Vs)
       #then #substituteList(K, M, vars(FEVs))
       #else #substituteList(#rebind(K,vars(Vs),#getVars(K),vars(FEVs keys M)),
                             M, vars(FEVs))
       #fi


  syntax K ::= #rebind(K, K, K, K) [function]
  rule #rebind(K:K, vars(BVs:Set), vars(AVs:Set), vars(FEVs:Set))
    => #rebind1(K, #freshSubst(BVs, AVs FEVs, .Map))

  syntax K ::= #freshSubst(Set, Set, Map)  [function]
  rule #freshSubst(SetItem(X:K) BVs:Set, AVs:Set, M:Map)
    => #freshSubst1(BVs, AVs, M, X, #freshVar(#getSymLabel(K2Sort(X)), AVs))
  rule #freshSubst(.Set, _, M:Map)
    => #substMap(M)

  syntax K ::= #substMap(Map)

  syntax K ::= #rebind1(K, K) [function]
  rule #rebind1(L:KLabel(Ks:List{K}), #substMap(M:Map))
    => #rebind2(L(Ks), 1, M, L(.List{K}))

  syntax K ::= #rebind2(K, Int, Map, K) [function]
  rule #rebind2(L:KLabel(K:K,, Ks:List{K}), I:Int, M:Map, L(Ks':List{K}))
    => #if (isBound(L,I) ==K true)
//        orBool (isBound(L,I) ==K "star")
        orBool (isBounding(L, I) ==K true)
       #then #rebind2(L(Ks), I +Int 1, M, L(Ks',, #substitutePlain(K, M)))
       #else #rebind2(L(Ks), I +Int 1, M, L(Ks',, K))
       #fi
  rule #rebind2(_:KLabel(.List{K}), _, _, K:K) => K
    

  syntax K ::= #freshSubst1(Set, Set, Map, K, K) [function]
  rule #freshSubst1(BVs:Set, AVs:Set, M:Map, X:K, Y:K)
    => #freshSubst(BVs, SetItem(Y) AVs, M X |-> Y)

  syntax K ::= #substitutePlain(K, Map) [function]
             | #substitutePlainList(K, Map) [function]
             | #substitutePlainList1(K, Map, List{K}) [function]


  rule #substitutePlain(X:K, X:K |-> Y:K _) => Y
  rule #substitutePlain(K:K, M:Map) => #substitutePlainList(K, M)
    when isId(K) =/=K true orElseBool $hasMapping(M, K) =/=K true

  rule #substitutePlainList(L:KLabel(Ks:List{K}), M:Map)
    => #substitutePlainList1(L:KLabel(Ks), M, .List{K})
  
  rule #substitutePlainList1(_:KLabel((K:K => .List{K}),,_), M:Map, _,,
        (.List{K} => #substitutePlain(K,M)))
  rule #substitutePlainList1(L:KLabel(.List{K}), _, Ks:List{K}) => L(Ks)


// Grigore: I added the operation below here, because I want it to be
// generic.  I don't know how to generate globablly fresh variables
// of desired type any other way ... sorry.  This is used in type inference
  syntax K ::= freshVariables(Set,K)
  rule freshVariables(.Set, T) => T
  rule freshVariables(SetItem(Tv) S:Set, T)
    => freshVariables(S, T[#changeLabel(Tv',Tv)/Tv])
    when fresh(Tv':K)

  syntax K ::= #changeLabel(K,K)  [function]
  rule #changeLabel(L:KLabel(Ks:List{K}),L':KLabel(_)) => L'(Ks)

endmodule
