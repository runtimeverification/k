// Copyright (c) 2014 K Team. All Rights Reserved.
module MY-PATTERN-MATCHING

// adapted from k-prelude.k
  syntax KItem ::= #myMap(Map)
  syntax Bool ::= #myIsMapInK(K)      [function]
  syntax Map ::= #myGetMapFromK(K)  [function]

  rule #myIsMapInK(#myMap(_)) => true
  rule #myIsMapInK(_) => false  [owise]  // YilongL: avoid partial function that gets stuck and fails the Java rewrite engine assertion
  rule #myGetMapFromK(#myMap(M:Map)) => M

/***********
  VISIBLE
***********/
// Tells if a matching exists
  syntax Bool ::= myIsMatching(KList, KList)            [function]
  rule myIsMatching(Ps:KList, Ks:KList)
    => #myIsMapInK(#myPatternMatch(Ps,Ks)) ==K true

// Gets the matching; call myIsMatching first, for safety
  syntax Map ::= myGetMatching(KList, KList)          [function]
  rule myGetMatching(Ps:KList, Ks:KList)
    => #myGetMapFromK(#myPatternMatch(Ps,Ks))

// Tells how to decompose pattern matching
  syntax KList ::= myDecomposeMatching(KList, KList)    [function]
  syntax KItem ::= myDoneDecomposeMatching(Variable, K)
  syntax KItem ::= #unmatchableError(KList, KList)
// Here are some basic decomposition rules, but one can add more
//  rule myDecomposeMatching((L:KLabel(Ps:KList) => Ps), (L(Ks:KList) => Ks))
// TODO(Yilong): current impl. assumes that rewrite has been pushed to the top
  rule myDecomposeMatching(L:KLabel(Ps:KList), L(Ks:KList)) => myDecomposeMatching(Ps, Ks)
    when isVariable(L(Ps)) =/=K true
  rule myDecomposeMatching(P:Variable, K) => myDoneDecomposeMatching(P, K)
  rule myDecomposeMatching(P:K,,Ps:KList, K:K,,Ks:KList)
       => myDecomposeMatching(P, K),,myDecomposeMatching(Ps, Ks)
    //when Ps =/=KList .KList
    // TODO(YilongL): the current impl. of term inequality cannot handle non-ground arguments
    when notBool emptyKList(Ps)
  // rule myDecomposeMatching(.KList, .KList) => .KList
  // TODO(YilongL): builtins in Java rewrite engine may not be represented as KItem's
  rule myDecomposeMatching(Ps:KList, Ps:KList)
    => .KList
  rule myDecomposeMatching(Ps:KList, Ks:KList)
    => #unmatchableError(Ps,Ks) requires Ps =/=KList Ks [owise]

// For example, one may add rules like the following in one's language
//  rule myDecomposeMatching(([P:Exp|T:Exp] => P,T),([V:Val,Vs:Vals] => V,[Vs]))

  syntax Bool ::= emptyKList(KList)  [function]
  rule emptyKList(.KList) => true
  rule emptyKList(K,,Ks) => false
/***********
  HIDDEN
***********/

  // Subsorting ids to variables for matching purposes.
  syntax Variable ::= Id

  syntax KItem ::= #myPatternMatch(KList, KList)   [function]
  rule #myPatternMatch(Ps:KList, Ks:KList)
    => #myPatternMatch1(myDecomposeMatching(Ps,Ks), .Map)

  syntax KItem ::= #myPatternMatch1(KList, Map)  [function]
  syntax KItem ::= "#nonlinearPatternError"
//  rule #myPatternMatch1((myDecomposeMatching(X:Variable,K:K) => .KList),,_,
//                      (M:Map, (.Map => X |-> K)))
  rule #myPatternMatch1(myDoneDecomposeMatching(X:Variable,K:K),,Ps, M:Map) // YilongL: use myDoneDecomposeMatching
    => #myPatternMatch1(.KList,,Ps, (X |-> K M:Map))
    when notBool (X in keys(M))  // only linear patterns allowed for now
  rule #myPatternMatch1(#unmatchableError(P,K),,_, _:Map)
    => #unmatchableError(P,K)
  rule #myPatternMatch1(myDoneDecomposeMatching(X:Variable,K:K),,Ps, M:Map)
    => #nonlinearPatternError
    when X in keys(M)  // TODO(YilongL): this side condition contains two function calls which can be combined into one instead
  rule #myPatternMatch1(.KList, M:Map) => #myMap(M)


endmodule
