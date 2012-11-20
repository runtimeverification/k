
module BINDER
  imports BUILTIN-HOOKS
  syntax KLabel ::= "isBinder"
  syntax Bool ::= isBound(KLabel, Int)  [function]
  syntax Bool ::= isBounding(KLabel, Int) [function]

  syntax K ::= splitedBinder(List{K}, List{K}, Set)

  syntax Bool ::= K "inVars" K [function]
  rule K inVars vars(S) => K in S

  syntax K ::= boundedVars(K) [function]
  rule boundedVars(K) => boundedVars1(binderSplit(K))
  
  syntax K ::= boundedVars1(K) [function]
  rule boundedVars1(splitedBinder(NBEs, BEs, Bound))
    => vars(Bound)

  syntax K ::= binderSplit(K) [function]
  rule binderSplit(L:KLabel(Ks))
    => binderSplit1(L, 1, Ks, .List{K}, .List{K}, .Set)

  syntax K ::= binderSplit1(KLabel, Int, List{K}, List{K}, List{K}, Set) [function]
  rule binderSplit1(L, I, K,,Ks, NBEs, BEs, Bound)
    => #if isBound(L,I) ==K true
       #then binderSplit1(L, I +Int 1, Ks, NBEs, BEs, Bound SetItem(K))
       #else #if isBounding(L, I) ==K true
             #then binderSplit1(L, I +Int 1, Ks, NBEs, BEs,,K, Bound)
             #else binderSplit1(L, I +Int 1, Ks, NBEs,,K, BEs, Bound)
             #fi 
       #fi
  rule binderSplit1(L, I, .List{K}, NBEs, BEs, Bound)
    => splitedBinder(NBEs, BEs, Bound)

  
endmodule

module FREE-VARS
  imports BINDER 

  syntax FreshVar ::= "#freshVar" "(" Int ")" [klabel(#freshvar)]
  syntax Id ::= FreshVar

  syntax K ::= freshVar(Set) [function]
  rule freshVar(Ks) => freshVar1(Ks, #freshVar(1))

  syntax K ::= freshVar1(Set, K) [function]
  rule freshVar1(.Set, K) => K
  rule freshVar1(SetItem(#freshVar(I1:Int)) Ks, #freshVar(I2:Int))
    => #if I1 >=Int I2 ==K true 
       #then freshVar1(Ks, #freshVar(I1 +Int 1))
       #else freshVar1(Ks, #freshVar(I2))
       #fi 
  rule freshVar1((SetItem(K) => .Set) Ks, _)
    when isFreshVar(K) =/=K true

  syntax K ::= freeVars(List{K}) [function]
  rule freeVars(K) => freeVars(K, .Set, .Set)
  
  syntax K ::= freeVars(List{K}, Set, Set) [function]
  rule freeVars(.List{K}, Bound, Free) => vars(Free) 
  rule freeVars(X:Id,, Ks, Bound:Set, Free:Set)
    => #if X in Bound ==K true #then freeVars(Ks, Bound, Free)
       #else freeVars(Ks, Bound, Free SetItem(X)) #fi
  rule freeVars((L:KLabel(Ks:List{K}) => Ks),, _, _, _)
    when isId(L(Ks)) =/=K true andBool isBinder(L(Ks)) =/=K true
  rule freeVars(K,, Ks, Bound, Free) 
    =>  freeVars1(Ks, freeVarsBinder(K, Bound), Bound, Free)
    when isBinder(K)

  syntax K ::= freeVars1(List{K}, K, Set, Set) [function]
  rule freeVars1(Ks, vars(Free1), Bound, Free2)
    => freeVars(Ks, Bound, Free1 Free2)

  syntax K ::= freeVarsBinder(K, Set) [function]
  rule freeVarsBinder(K, Bound)
    => freeVarsBinder1(binderSplit(K), Bound)

  syntax K ::= freeVarsBinder1(K, Set) [function]
  rule freeVarsBinder1(splitedBinder(NBEs, BEs, Bound1), Bound)
    => freeVarsBinder2(freeVars(NBEs, Bound, .Set), freeVars(BEs, Bound1 Bound, .Set))

  syntax K ::= freeVarsBinder2(K, K) [function]
  rule freeVarsBinder2(vars(Free1), vars(Free2)) => vars(Free1 Free2)

endmodule

module SUBSTITUTION 
  imports FREE-VARS
  syntax K ::= substitute(K, K, K) [function]
             | substituteList(K, K, K) [function]
             | substituteList1(K, K, K, List{K}) [function]
  
  rule substituteList(K, X, E) => substituteList1(K, X, E, .List{K})
  rule substituteList1(L((K => .List{K}),,_), X, E, _,,(.List{K} => substitute(K, X, E)))
  rule substituteList1(L(.List{K}), X, E, Ks) => L(Ks)
  
  rule substitute(X, X, E) => E
  rule substitute(K, X, E) => substituteList(K, X, E)
    when isId(K) =/=K true andBool isBinder(K) =/=K true

  rule substitute(K, X, E) => substituteBinder(K, X, E) 
    when isBinder(K)

  syntax K ::= substituteBinder(K, K, K) [function]
  rule substituteBinder(K, X, E) 
    => substituteBinder1(K, X, E, boundedVars(K), freeVars(E))

  syntax K ::= substituteBinder1(K, K, K, K, K) [function]
  rule substituteBinder1(K, X, E, vars(BKVs), vars(FEVs))
    => #if X in BKVs ==K true 
       #then E
       #else substituteBinder2(K, X, E, vars(intersectSet(BKVs, FEVs)), vars(FEVs))
       #fi

  syntax K ::=  substituteBinder2(K, K, K, K, K) [function]
  rule substituteBinder2(K, X, E, vars(Vs), vars(FEVs))
    => #if isEmptySet(Vs) 
       #then substituteList(K, X,E)
       #else substituteList(rebind(K, vars(Vs), getVars(K)), X, E)
       #fi 


  syntax K ::= rebind(K, K, K) [function]
  rule rebind(K, vars(BVs), vars(AVs))
    => rebind1(K, freshSubst(BVs, AVs, .Map))

  syntax K ::= freshSubst(Set, Set, Map)
  rule freshSubst(SetItem(X:Id) BVs, AVs:Set, M)
    => freshSubst1(SetItem(X:Id) BVs, AVs, M, freshVar(AVs))
  rule freshSubst(.Set, _, M) 
    => substMap(M)

  syntax K ::= substMap(Map)

  syntax K ::= rebind1(K, K) [function]
  rule rebind1(L(Ks), substMap(M))
    => rebind2(L(Ks), 1, M, L(.List{K}))

  syntax K ::= rebind2(K, Int, Map, K) [function]
  rule rebind2(L(K,, Ks), I, M, L(Ks'))
    => #if isBound(L,I) ==K true orBool isBounding(L, I) ==K true
       #then rebind2(L(Ks), I +Int 1, M, L(Ks',, applySubstMap(K, M)))
       #else rebind2(L(Ks), I +Int 1, M, L(Ks',, K))
       #fi
  rule rebind2(L(.List{K}), _, _, L(Ks)) => L(Ks)
    

  syntax K ::= freshSubst1(Set, Set, Map, K)
  rule freshSubst1(SetItem(X:Id) BVs, AVs, M, Y)
    => freshSubst(BVs, SetItem(Y) AVs, M X |-> Y)

  syntax K ::= applySubstMap(K, Map) [function]
             | applySubstMapList(K, Map) [function]
             | applySubstMapList1(K, Map, List{K}) [function]


  rule applySubstMap(X, X |-> Y M) => Y
  rule applySubstMap(K:K, M:Map) => applySubstMapList(K, M)
    when isId(K) =/=K true orElseBool $hasMapping(M, K) =/=K true

  rule applySubstMapList(L:KLabel(Ks), M)
    => applySubstMapList1(L:KLabel(Ks), M, .List{K})
  
  rule applySubstMapList1(L:KLabel((K => .List{K}),,Ks), M, Ks',,
        (.List{K} => applySubstMap(K,M)))
  rule applySubstMapList1(L:KLabel(.List{K}), _, Ks) => L(Ks)

 // if  and  is not in the free variables of  (sometimes said  is fresh for ).
  
endmodule
