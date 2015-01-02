// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "builtins/k-equal.k"

module PATTERN-MATCHING
  imports K-EQUAL-HOOKS
  imports ID-SYNTAX-HOOKS

// adapted from k-prelude.k
  syntax KItem ::= #map(Map)
  syntax Bool ::= #isMapInK(K)      [function]
  syntax Map ::= #getMapFromK(K)  [function]

  rule #isMapInK(#map(_)) => true
  rule #isMapInK(_) => false  [owise]  // YilongL: avoid partial function that gets stuck and fails the Java rewrite engine assertion
  rule #getMapFromK(#map(M:Map)) => M

/***********
  VISIBLE
***********/
// Tells if a matching exists
  syntax Bool ::= isMatching(KList, KList)            [function]
  rule isMatching(Ps:KList, Ks:KList)
    => #isMapInK(#patternMatch(Ps,Ks)) ==K true

// Gets the matching; call isMatching first, for safety
  syntax Map ::= getMatching(KList, KList)          [function]
  rule getMatching(Ps:KList, Ks:KList)
    => #getMapFromK(#patternMatch(Ps,Ks))

// Tells how to decompose pattern matching
  syntax KList ::= decomposeMatching(KList, KList)    [function]
  syntax KItem ::= doneDecomposeMatching(Variable, K)
  syntax KItem ::= #unmatchableError(KList, KList)
// Here are some basic decomposition rules, but one can add more
//  rule decomposeMatching((L:KLabel(Ps:KList) => Ps), (L(Ks:KList) => Ks))
// TODO(Yilong): current impl. assumes that rewrite has been pushed to the top
  rule decomposeMatching(L:KLabel(Ps:KList), L(Ks:KList)) => decomposeMatching(Ps, Ks)
    when isVariable(L(Ps)) =/=K true
  rule decomposeMatching(P:Variable, K) => doneDecomposeMatching(P, K)
  rule decomposeMatching(P:K,,Ps:KList, K:K,,Ks:KList)
       => decomposeMatching(P, K),,decomposeMatching(Ps, Ks)
    //when Ps =/=KList .KList
    // TODO(YilongL): the current impl. of term inequality cannot handle non-ground arguments
    when notBool emptyKList(Ps)
  // rule decomposeMatching(.KList, .KList) => .KList
  // TODO(YilongL): builtins in Java rewrite engine may not be represented as KItem's
  rule decomposeMatching(Ps:KList, Ps:KList)
    => .KList
  rule decomposeMatching(Ps:KList, Ks:KList)
    => #unmatchableError(Ps,Ks) requires Ps =/=KList Ks [owise]

// For example, one may add rules like the following in one's language
//  rule decomposeMatching(([P:Exp|T:Exp] => P,T),([V:Val,Vs:Vals] => V,[Vs]))

  syntax Bool ::= emptyKList(KList)  [function]
  rule emptyKList(.KList) => true
  rule emptyKList(K:K,,KL) => false
/***********
  HIDDEN
***********/

  // Subsorting ids to variables for matching purposes.
  syntax Variable ::= Id

  syntax KItem ::= #patternMatch(KList, KList)   [function]
  rule #patternMatch(Ps:KList, Ks:KList)
    => #patternMatch1(decomposeMatching(Ps,Ks), .Map)

  syntax KItem ::= #patternMatch1(KList, Map)  [function]
  syntax KItem ::= "#nonlinearPatternError"
//  rule #patternMatch1((decomposeMatching(X:Variable,K:K) => .KList),,_,
//                      (M:Map, (.Map => X |-> K)))
  rule #patternMatch1(doneDecomposeMatching(X:Variable,K:K),,Ps, M:Map) // YilongL: use doneDecomposeMatching
    => #patternMatch1(.KList,,Ps, (X |-> K M:Map))
    when notBool (X in keys(M))  // only linear patterns allowed for now
  rule #patternMatch1(#unmatchableError(P,K),,_, _:Map)
    => #unmatchableError(P,K)
  rule #patternMatch1(doneDecomposeMatching(X:Variable,K:K),,Ps, M:Map)
    => #nonlinearPatternError
    when X in keys(M)  // TODO(YilongL): this side condition contains two function calls which can be combined into one instead
  rule #patternMatch1(.KList, M:Map) => #map(M)


endmodule
