require "builtins/k-equal.k"

module PATTERN-MATCHING
   imports K-EQUAL-HOOKS

/***********
  VISIBLE
***********/

// Tells if a matching exists
  syntax Bool ::= isMatching(KList, KList)            [function]
  rule isMatching(Ps:KList, Ks:KList)
    => #isMapInK(#patternMatch(Ps,Ks)) ==K true

// Gets the matching; call isMatching first, for safety
  syntax Map  ::= getMatching(KList, KList)           [function]
  rule getMatching(Ps:KList, Ks:KList)
    => #getMapFromK(#patternMatch(Ps,Ks))

// Tells how to decompose pattern matching
  syntax KList ::= decomposeMatching(KList, KList)  [function]
// Here are some basic decomposition rules, but one can add more
  rule decomposeMatching((L:KLabel(Ps:KList) => Ps), (L(Ks:KList) => Ks))
    when isVariable(L(Ps)) =/=K true
  rule decomposeMatching(P:K,,Ps:KList, K:K,,Ks:KList)
       => decomposeMatching(P,K),,decomposeMatching(Ps,Ks)
    when Ps =/=KList .KList
  rule decomposeMatching(.KList, .KList) => .KList
// For example, one may add rules like the following in one's language
//  rule decomposeMatching(([P:Exp|T:Exp] => P,T),([V:Val,Vs:Vals] => V,[Vs]))

/***********
  HIDDEN
***********/

  // Subsorting ids to variables for matching purposes.
  syntax Variable ::= Id

  syntax K ::= #patternMatch(KList, KList)   [function]
  rule #patternMatch(Ps:KList, Ks:KList)
    => #patternMatch1(decomposeMatching(Ps,Ks), .Map)

  syntax K ::= #patternMatch1(KList, Map)  [function]
  rule #patternMatch1((decomposeMatching(X:Variable,K:K) => .KList),,_,
                      M:Map (.Map => X |-> K))
    when notBool $hasMapping(M,X)  // only linear patterns allowed for now
  rule #patternMatch1(.KList, M:Map) => #map(M)

endmodule
