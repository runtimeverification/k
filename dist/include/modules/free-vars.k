
/*
 *
 *  sort Variable - all possible variables
 *
 *  freshLabel(KLabel, Int) ~> '#symSort(.List{K})
 *
 */


module VARIABLE
  imports SYMBOLIC-K

  syntax K ::= vars(Set)

  syntax K ::= getVars(K)  [function]
  rule getVars(K:K) => getVars1(K, .Set)

  syntax K ::= getVars1(List{K}, Set) [function]
  rule getVars1((X:Variable => .List{K}),,_, _ (.Set => SetItem(X)))
  rule getVars1((L:KLabel(Ks:List{K}) => Ks),,_, _)
    when isVariable(L(Ks)) =/=K true
  rule getVars1(.List{K}, S:Set) => vars(S)


  syntax K ::= getStarVars(Bool, K) [function]
  rule getStarVars(true, K:K) => getVars(K)
  rule getStarVars(false, V:Variable) => vars(SetItem(V))
  
  syntax K ::= getSymLabel(String) [function]
  rule getSymLabel(Type:String) => String2KLabel("'#sym" +String Type)(.List{K})

  syntax K ::= freshVar(K, Set) [function]
  rule freshVar(L:KLabel(_), Ks:Set) => freshVar1(Ks, L("local",,1))

  syntax K ::= freshVar1(Set, K) [function]
  rule freshVar1(.Set, K:K) => K
  rule freshVar1(SetItem(L:KLabel("local",, I1:Int)) Ks:Set, L("local",, I2:Int))
    => #if I1 >=Int I2 ==K true 
       #then freshVar1(Ks, L("local",, I1 +Int 1))
       #else freshVar1(Ks, L("local",, I2))
       #fi 
  rule freshVar1((SetItem(K:K) => .Set) _, _)
    when isSymbolicK(K) =/=K true

endmodule


module BINDER
  imports VARIABLE
  syntax KLabel ::= "isBinder"
  syntax KLabel ::= "isStarBinder"
  syntax Bool ::= isBound(KLabel, Int)  [klabel("isBound"), function]
  syntax Bool ::= isBounding(KLabel, Int) [klabel("isBounding"), function]

  syntax K ::= splitedBinder(List{K}, List{K}, Set)

  syntax Bool ::= K "inVars" K [function]
  rule K:K inVars vars(S:Set) => K in S

  syntax K ::= boundedVars(K) [function]
  rule boundedVars(K:K) => boundedVars1(binderSplit(isStarBinder(K) ==K true, K))
  
  syntax K ::= boundedVars1(K) [function]
  rule boundedVars1(splitedBinder(_, _, Bound:Set))
    => vars(Bound)

  syntax K ::= binderSplit(Bool, K) [function]
  rule binderSplit(T:Bool, L:KLabel(Ks:List{K}))
    => binderSplit1(T, L, 1, Ks, .List{K}, .List{K}, .Set)

  syntax K ::= binderSplit1(Bool, KLabel, Int, List{K}, List{K}, List{K}, Set) 
     [function]
  rule binderSplit1(T:Bool, L:KLabel, I:Int, K:K,,Ks:List{K}, NBEs:List{K}, BEs:List{K}, Bound:Set)
    => #if isBound(L,I) ==K true
       #then binderSplit2(T, L, I +Int 1, Ks, NBEs, BEs, Bound, getStarVars(T, K))
       #else #if isBounding(L, I) ==K true
             #then binderSplit1(T, L, I +Int 1, Ks, NBEs, BEs,,K, Bound)
             #else binderSplit1(T, L, I +Int 1, Ks, NBEs,,K, BEs, Bound)
             #fi 
       #fi
  rule binderSplit1(_, _, _, .List{K}, NBEs:List{K}, BEs:List{K}, Bound:Set)
    => splitedBinder(NBEs, BEs, Bound)

  syntax K ::= binderSplit2(Bool, KLabel, Int, List{K}, List{K}, List{K}, Set, K) [function]
  rule binderSplit2(T:Bool, L:KLabel, I:Int, Ks:List{K}, NBEs:List{K}, BEs:List{K}, Bound:Set, vars(Bound':Set))
    => binderSplit1(T, L, I, Ks, NBEs, BEs, Bound Bound')
  
endmodule

module FREE-VARS
  imports BINDER 

  syntax K ::= freeVars(List{K}) [function]
  rule freeVars(Ks:List{K}) => freeVars(Ks:List{K}, .Set, .Set)
  
  syntax K ::= freeVars(List{K}, Set, Set) [function]
  rule freeVars(.List{K}, _, Free:Set) => vars(Free)
  rule freeVars(X:Variable,,Ks:List{K}, Bound:Set, Free:Set)
    => #if X in Bound ==K true #then freeVars(Ks, Bound, Free)
       #else freeVars(Ks, Bound, Free SetItem(X)) #fi
  rule freeVars((L:KLabel(Ks:List{K}) => Ks),, _, _, _)
    when isVariable(L(Ks)) =/=K true andBool isBinder(L(Ks)) =/=K true
  rule freeVars(K:K,,Ks:List{K}, Bound:Set, Free:Set)
    =>  freeVars1(Ks, freeVarsBinder(K, Bound), Bound, Free)
    when isBinder(K)

  syntax K ::= freeVars1(List{K}, K, Set, Set) [function]
  rule freeVars1(Ks:List{K}, vars(Free1:Set), Bound:Set, Free2:Set)
    => freeVars(Ks, Bound, Free1 Free2)

  syntax K ::= freeVarsBinder(K, Set) [function]
  rule freeVarsBinder(K:K, Bound:Set)
    => freeVarsBinder1(binderSplit(isStarBinder(K) ==K true, K), Bound)

  syntax K ::= freeVarsBinder1(K, Set) [function]
  rule freeVarsBinder1(splitedBinder(NBEs:List{K}, BEs:List{K}, Bound1:Set), Bound:Set)
    => freeVarsBinder2(freeVars(NBEs, Bound, .Set), freeVars(BEs, Bound1 Bound, .Set))

  syntax K ::= freeVarsBinder2(K, K) [function]
  rule freeVarsBinder2(vars(Free1:Set), vars(Free2:Set)) => vars(Free1 Free2)

endmodule

module SUBSTITUTION 
  imports FREE-VARS
  syntax K ::= substitutionError(K,String)
  syntax K ::= K "[" K "/" Variable "]" [function]
  rule K:K[E:K/V:Variable] => substitute(K, V, E)
  rule _[_/V:K] 
    => substitutionError(V, "is not a Variable; cannot substitute")
    when isVariable(V) =/=K true

  syntax K ::= substitute(K, K, K) [function]
             | substituteList(K, K, K) [function]
             | substituteList1(K, K, K, List{K}) [function]
  
  rule substituteList(K:K, X:K, E:K) => substituteList1(K, X, E, .List{K})
  rule substituteList1(_:KLabel((K:K => .List{K}),,_), X:K, E:K, _,,(.List{K} => substitute(K, X, E)))
  rule substituteList1(L:KLabel(.List{K}), _, _, Ks:List{K}) => L(Ks)
  
  rule substitute(Y:Variable, X:Variable, E:K) 
    => #if X ==K Y #then E #else Y #fi
  rule substitute(K:K, X:K, E:K) => substituteList(K, X, E)
    when isVariable(K) =/=K true andBool isBinder(K) =/=K true

  rule substitute(K:K, X:K, E:K) => substituteBinder(K, X, E) 
    when isBinder(K)

  syntax K ::= substituteBinder(K, K, K) [function]
  rule substituteBinder(K:K, X:K, E:K) 
    => substituteBinder1(K, X, E, boundedVars(K), freeVars(E))

  syntax K ::= substituteBinder1(K, K, K, K, K) [function]
  rule substituteBinder1(K:K, X:K, E:K, vars(BKVs:Set), vars(FEVs:Set))
    => #if X in BKVs ==K true 
       #then K
       #else substituteBinder2(K, X, E, vars(intersectSet(BKVs, FEVs)), vars(FEVs))
       #fi

  syntax K ::=  substituteBinder2(K, K, K, K, K) [function]
  rule substituteBinder2(K:K, X:K, E:K, vars(Vs:Set), vars(FEVs:Set))
    => #if isEmptySet(Vs) 
       #then substituteList(K, X,E)
       #else substituteList(rebind(K, vars(Vs), getVars(K), vars(FEVs SetItem(X))), X, E)
       #fi 


  syntax K ::= rebind(K, K, K, K) [function]
  rule rebind(K:K, vars(BVs:Set), vars(AVs:Set), vars(FEVs:Set))
    => rebind1(K, freshSubst(BVs, AVs FEVs, .Map))

  syntax K ::= freshSubst(Set, Set, Map)  [function]
  rule freshSubst(SetItem(X:K) BVs:Set, AVs:Set, M:Map)
    => freshSubst1(BVs, AVs, M, X, freshVar(getSymLabel(K2Sort(X)), AVs))
  rule freshSubst(.Set, _, M:Map) 
    => substMap(M)

  syntax K ::= substMap(Map)

  syntax K ::= rebind1(K, K) [function]
  rule rebind1(L:KLabel(Ks:List{K}), substMap(M:Map))
    => rebind2(L(Ks), 1, M, L(.List{K}))

  syntax K ::= rebind2(K, Int, Map, K) [function]
  rule rebind2(L:KLabel(K:K,, Ks:List{K}), I:Int, M:Map, L(Ks':List{K}))
    => #if isBound(L,I) ==K true orBool isBounding(L, I) ==K true
       #then rebind2(L(Ks), I +Int 1, M, L(Ks',, applySubstMap(K, M)))
       #else rebind2(L(Ks), I +Int 1, M, L(Ks',, K))
       #fi
  rule rebind2(_:KLabel(.List{K}), _, _, K:K) => K
    

  syntax K ::= freshSubst1(Set, Set, Map, K, K) [function]
  rule freshSubst1(BVs:Set, AVs:Set, M:Map, X:K, Y:K)
    => freshSubst(BVs, SetItem(Y) AVs, M X |-> Y)

  syntax K ::= applySubstMap(K, Map) [function]
             | applySubstMapList(K, Map) [function]
             | applySubstMapList1(K, Map, List{K}) [function]


  rule applySubstMap(X:K, X:K |-> Y:K _) => Y
  rule applySubstMap(K:K, M:Map) => applySubstMapList(K, M)
    when isId(K) =/=K true orElseBool $hasMapping(M, K) =/=K true

  rule applySubstMapList(L:KLabel(Ks:List{K}), M:Map)
    => applySubstMapList1(L:KLabel(Ks), M, .List{K})
  
  rule applySubstMapList1(_:KLabel((K:K => .List{K}),,_), M:Map, _,,
        (.List{K} => applySubstMap(K,M)))
  rule applySubstMapList1(L:KLabel(.List{K}), _, Ks:List{K}) => L(Ks)

 // if  and  is not in the free variables of  (sometimes said  is fresh for ).
  
endmodule
