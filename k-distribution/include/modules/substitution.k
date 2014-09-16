// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "pattern-matching.k"
require "builtins/symbolic-k.k"
require "k-prelude.k"

module VARIABLE
  imports SYMBOLIC-K

  syntax K ::= isCollection(K) [function]
  rule isCollection(_:Set) => true
  rule isCollection(_:List) => true
  rule isCollection(_:Map) => true

// Get the variables in a K term, going through the sets Klabeled as
// terms as well, if any.
// Grigore: We should also have a user-friendly variant of this, which
// returns an actual set of variables.  Well, I just added it, please check.

  syntax Set ::= getVariables(K)  [function]  // public
  rule getVariables(K:K) => #getVars(K)

  syntax Set ::= #getVars(K)  [function]
  rule #getVars(K:K) => #getVars1(K, .Set)

  syntax Set ::= #getVars1(KList, Set)  [function]
  rule #getVars1((X:Variable => .KList),,_, (.Set => SetItem(X)) _:Set)
  rule #getVars1((L:KLabel(Ks:KList) => Ks),,_, _)
    when (isVariable(L(Ks)) =/=K true) andBool
         (isCollection(L(Ks)) =/=K true)
  rule #getVars1(.KList, S:Set) => S
  rule #getVars1((.KList => I:K),,(ListItem(I) => .List) _:List,,_, _)
  rule #getVars1((.List => .KList),,_, _)
  rule #getVars1((.KList => I:K),,(SetItem(I) => .Set) _:Set,,_, _)
  rule #getVars1((.Set => .KList),,_, _)
  rule #getVars1((.KList => Key:K,,Value:K),,(Key |-> Value => .Map) _:Map,,_, _)
  rule #getVars1((.Map => .KList),,_, _)
  rule #getVars1((K1:KItem ~> K2:KItem ~> K:K => K1,,K2,,K),,_, _)
  rule #getVars1((.K => .KList),,_, _)

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
  rule #freshVar1((SetItem(K:K) => .Set) _:Set, _)
    when isLocalFreshVar(K) =/=K true

  syntax Bool ::= isLocalFreshVar(K)  [function]
  rule isLocalFreshVar(_:KLabel("local",,_:Int)) => true

endmodule


module BINDER
  imports VARIABLE
  syntax KLabel ::= "isBinder"

// Grigore: we should check why we get kompile errors when we
// remove the klabels below; they should be the default labels ...
  syntax Bool ::= isBound(KLabel, Int)  [klabel("isBound"), function]
  syntax Bool ::= isBounding(KLabel, Int) [klabel("isBounding"), function]

  syntax KItem ::= #splitedBinder(KList, KList, Set)

  syntax K ::= #boundVars(K)  [function]
  rule #boundVars(K:K) => #boundVars1(#binderSplit(K))

  syntax Set ::= #boundVars1(K)  [function]
  rule #boundVars1(#splitedBinder(_, _, Bound:Set))
    => Bound

  syntax K ::= #binderSplit(K)  [function]
  rule #binderSplit(L:KLabel(Ks:KList))
    => #binderSplit1(L, 1, Ks, .KList, .KList, .Set)

  syntax K ::= #binderSplit1(KLabel,Int,KList,KList,KList,Set)  [function]
  rule #binderSplit1(L:KLabel, I:Int, K:K,,Ks:KList,
                     NBEs:KList, BEs:KList, Bound:Set)
    => #if isBound(L,I) ==K true
       #then #binderSplit1(L, I +Int 1, Ks, NBEs, BEs, Bound #getVars(K))
       #else #if isBounding(L, I) ==K true
             #then #binderSplit1(L, I +Int 1, Ks, NBEs, (BEs,,K), Bound)
             #else #binderSplit1(L, I +Int 1, Ks, (NBEs,,K), BEs, Bound)
             #fi
       #fi
  rule #binderSplit1(_, _, .KList, NBEs:KList, BEs:KList, Bound:Set)
    => #splitedBinder(NBEs, BEs, Bound)

endmodule

module FREE-VARS
  imports BINDER

/* // TODO: (radum) deleted these from k-prelude.k and are required by substitution
  syntax K ::= Set2KTerm(Set)        [function]
  rule Set2KTerm(S:Set) => Set2KTermAcc(S, #set(.KList))

  syntax K ::= Set2KTermAcc(Set, K)  [function]
  rule Set2KTermAcc((SetItem(K:K) => .Set)_, _(_,,(.KList => K))) [nojava]
  rule Set2KTermAcc(.Set, K:K) => K
*/
  syntax Set ::= freeVariables(KList)  [function, latex({\it FV}({#1}))]  // public
  rule freeVariables(Ks:KList) => #freeVars(Ks)

// Grigore: again, I think this should just return a set of variables, not a K
// I added a user-interface variant of it above.  I use it in type-inference.
  syntax Set ::= #freeVars(KList)  [function]
  rule #freeVars(Ks:KList) => #freeVars(Ks:KList, .Set, .Set)

  syntax Set ::= #freeVars(KList, Set, Set)  [function, klabel(#freevars2)]
  rule #freeVars(.KList, _, Free:Set) => Free
  rule #freeVars(X:Variable,,Ks:KList, Bound:Set, Free:Set)
    => #if X in Bound ==K true #then #freeVars(Ks, Bound, Free) #else
     #freeVars(Ks, Bound, Free SetItem(X)) #fi
  rule #freeVars((L:KLabel(Ks:KList) => Ks),, _, _, _)
    when (isVariable(L(Ks)) =/=K true) andBool
         (isBinder(L(Ks)) =/=K true) andBool
         (isCollection(L(Ks)) =/=K true)
  rule #freeVars((.KList => I:K),, (ListItem(I) => .List) _:List,,_, _, _)
  rule #freeVars((.List => .KList),,_, _, _)
  rule #freeVars((.KList => I:K),, (SetItem(I) => .Set) _:Set,,_, _, _)
  rule #freeVars((.Set => .KList),,_, _, _)
  rule #freeVars((.KList => Key:K,,Value:K),, (Key |-> Value => .Map) _:Map,,_, _, _)
  rule #freeVars((.Map => .KList),,_, _, _)


  rule #freeVars(K:K,,Ks:KList, Bound:Set, Free:Set)
    => #freeVars(Ks, Bound, #freeVarsBinder(K, Bound) Free)
    when isBinder(K)
// Grigore: new in order to deal with cc(.K)
  rule #freeVars((.K => .KList),,_, _, _)
  rule #freeVars((K1:KItem ~> K2:KItem ~> K:K => K1,,K2,,K),,_, _, _)

  syntax Set ::= #freeVarsBinder(K, Set)  [function]
  rule #freeVarsBinder(K:K, Bound:Set)
    => #freeVarsBinder1(#binderSplit(K), Bound)

  syntax Set ::= #freeVarsBinder1(K, Set)  [function]
  rule #freeVarsBinder1(
          #splitedBinder(NBEs:KList, BEs:KList, Bound1:Set), Bound:Set)
    => #freeVars(NBEs, Bound, .Set) #freeVars(BEs, Bound1 Bound, .Set)

endmodule

module SUBSTITUTION
  imports FREE-VARS
  imports PATTERN-MATCHING
  imports MAP

// Seems unnecessary
//  syntax KItem ::= #substitutionError(K,String)

// "Public" interface

  syntax K ::= K "[" KList "/" KList "]"  [function, prefer]
  syntax K ::= K "[" Map "]"  [function, prefer]

  rule K:K[Ks:KList / Vs:KList] => #substitute(K,#patternMatch(Vs,Ks))
  rule K:K[M:Map] => #substitute(K, M)

//  rule _[_/V:K]
//    => #substitutionError(V, "is not a Variable; cannot #substitute")
//    when isVariable(V) =/=K true

  syntax K ::= #substitute(K, Map)  [function]
             | #substituteFV(K, Map, Set)  [function]
             | #substituteList(K, Map, Set)  [function]
             | #substituteList1(K, Map, Set, KList)  [function]

// Grigore: should add Set ::= #freeVars(Set)

  rule #substitute(K:K, M:Map)
    => #substituteFV(K, M, #freeVars(values(M)))

  rule #substituteFV(Y:Variable, M:Map Y |-> V, _) => V
  rule #substituteFV(Y:Variable, M:Map, _) => Y
    when Y in keys(M) =/=K true

  rule #substituteFV(K:K, M:Map, FV) => #substituteBinder(K, M, FV)
    when isBinder(K)
  rule #substituteFV(K:K, M:Map, FV) => #substituteList(K, M, FV)
    when isVariable(K) =/=K true andBool isBinder(K) =/=K true andBool
         isCollection(K) =/=K true

  rule #substituteFV(K:Set, M:Map, FV) => #substituteSet(K, M, FV, .Set)
  rule #substituteFV(K:List, M:Map, FV) => #substituteList(K, M, FV, .List)
  rule #substituteFV(K:Map, M:Map, FV) => #substituteMap(K, M, FV, .Map)

  syntax List ::= #substituteList(List, Map, Set, List)  [function, klabel(#substituteList2)]
  syntax Set ::= #substituteSet(Set, Map, Set, Set)  [function]
  syntax Map ::= #substituteMap(Map, Map, Set, Map)  [function]

  rule #substituteList(K:K,M:Map,FV) => #substituteList1(K,M,FV,.KList)
  rule #substituteList1(_:KLabel((K:K => .KList),,_),M:Map,FV:K,
                        _,,(.KList => #substituteFV(K, M, FV)))
  rule #substituteList1(L:KLabel(.KList), _, _, Ks:KList) => L(Ks)
// Grigore: new in order to deal with cc(.K)
  rule #substituteList1(.K, _, _, _) => .K
  rule #substituteList1(K1:KItem ~> K2:KItem ~> K, M:Map, FV:K, .KList)
    => #substituteKArrow(K1:KItem ~> K2:KItem ~> K, M:Map, FV:K, .K)

  syntax K ::= #substituteKArrow(K, Map, Set, K)  [function]
  rule #substituteKArrow(.K, M, FV, K) => K
  rule #substituteKArrow((K1:KItem => .K) ~> _, M:Map, FV, _ ~> (.K => #substituteFV(K1,M,FV)))

  syntax K ::= #substituteBinder(K, Map, Set)  [function]
  rule #substituteBinder(K:K, M:Map, FV)
    => #substituteBinder1(K, M, #boundVars(K), FV)

  syntax K ::= #substituteBinder1(K, Map, Set, Set)  [function]
  rule #substituteBinder1(K:K, M:Map, BKVs:Set, FEVs:Set)
    => #substituteBinder2(K,M,intersectSet(BKVs,FEVs keys(M)),FEVs)

  syntax K ::=  #substituteBinder2(K, Map, Set, Set)  [function]
  rule #substituteBinder2(K:K, M:Map, .Set, FEVs:Set)
    => #substituteList(K, M, FEVs)
  rule #substituteBinder2(K:K, M:Map, SetItem(I) Vs, FEVs:Set)
    => #substituteList(#rebind(K,SetItem(I) Vs,#getVars(K),FEVs keys(M)),
                             M, FEVs)

  syntax K ::= #rebind(K, Set, Set, Set) [function]
  rule #rebind(K:K, BVs:Set, AVs:Set, FEVs:Set)
    => #rebind1(K, #freshSubst(BVs, AVs FEVs, .Map))

  syntax K ::= #freshSubst(Set, Set, Map)  [function]
  rule #freshSubst(SetItem(X:K) BVs:Set, AVs:Set, M:Map)
    => #freshSubst1(BVs, AVs, M, X, #freshVar(#getSymLabel(K2Sort(X)), AVs))
  rule #freshSubst(.Set, _, M:Map)
    => M

  syntax K ::= #rebind1(K, Map) [function]
  rule #rebind1(L:KLabel(Ks:KList), M:Map)
    => #rebind2(L(Ks), 1, M, L(.KList))

  syntax K ::= #rebind2(K, Int, Map, K) [function]
  rule #rebind2(L:KLabel(K:K,, Ks:KList), I:Int, M:Map, L(Ks':KList))
    => #if (isBound(L,I) ==K true)
//        orBool (isBound(L,I) ==K "star")
        orBool (isBounding(L, I) ==K true)
       #then #rebind2(L(Ks), I +Int 1, M, L(Ks',, #substitutePlain(K, M)))
       #else #rebind2(L(Ks), I +Int 1, M, L(Ks',, K))
       #fi
  rule #rebind2(_:KLabel(.KList), _, _, K:K) => K


  syntax Map ::= #freshSubst1(Set, Set, Map, K, K) [function]
  rule #freshSubst1(BVs:Set, AVs:Set, M:Map, X:K, Y:K)
    => #freshSubst(BVs, SetItem(Y) AVs, M X |-> Y)

  syntax K ::= #substitutePlain(K, Map) [function]
             | #substitutePlainList(K, Map) [function]
             | #substitutePlainList1(K, Map, KList) [function]


  rule #substitutePlain(X:K, X:K |-> Y:K _) => Y
  rule #substitutePlain(K:K, M:Map) => #substitutePlainList(K, M)
    when isId(K) =/=K true orElseBool K in keys(M) =/=K true

  rule #substitutePlainList(L:KLabel(Ks:KList), M:Map)
    => #substitutePlainList1(L:KLabel(Ks), M, .KList)
  rule #substitutePlainList(.K, _) => .K

  rule #substitutePlainList1(_:KLabel((K:K => .KList),,_), M:Map, _,,
        (.KList => #substitutePlain(K,M)))
  rule #substitutePlainList1(L:KLabel(.KList), _, Ks:KList) => L(Ks)


// Grigore: I added the operation below here, because I want it to be
// generic.  I don't know how to generate globablly fresh variables
// of desired type any other way ... sorry.  This is used in type inference
  syntax KItem ::= freshVariables(Set,K)
  rule freshVariables(.Set, T) => T
  rule freshVariables(SetItem(Tv) S:Set, T)
    => freshVariables(S, T[#freshSym(Tv)/Tv])

/*
  syntax KItem ::= freshVariables(Set,K)
  rule freshVariables(.Set, T:K) => T
  rule freshVariables(SetItem(Tv:K) S:Set, T:K)
    => freshVariables(S, T[#changeLabel(!Tv',Tv)/Tv])

  syntax K ::= #changeLabel(K,K)  [function]
  rule #changeLabel(_:KLabel(Ks:KList),L':KLabel(_)) => L'(Ks)
*/
endmodule
