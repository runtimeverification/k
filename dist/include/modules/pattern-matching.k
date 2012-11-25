module PATTERN-MATCHING

/***********
  VISIBLE
***********/

// Tells if a matching exists
  syntax Bool ::= isMatching(List{K}, List{K})            [function]
  rule isMatching(Ps:List{K}, Ks:List{K})
    => #isMapInK(#patternMatch(Ps,Ks)) ==K true

// Gets the matching; call isMatching first, for safety
  syntax Map  ::= getMatching(List{K}, List{K})           [function]
  rule getMatching(Ps:List{K}, Ks:List{K})
    => #getMapFromK(#patternMatch(Ps,Ks))

// Tells how to decompose pattern matching
  syntax List{K} ::= decomposeMatching(List{K}, List{K})  [function]
// Here are some basic decomposition rules, but one can add more
  rule decomposeMatching((L:KLabel(Ps:List{K}) => Ps), (L(Ks:List{K}) => Ks))
    when isVariable(L(Ps)) =/=K true
  rule decomposeMatching(P:K,,Ps:List{K}, K:K,,Ks:List{K})
       => decomposeMatching(P,K),,decomposeMatching(Ps,Ks)
    when Ps =/=List{K} .List{K}
  rule decomposeMatching(.List{K}, .List{K}) => .List{K}
// For example, one may add rules like the following in one's language
//  rule decomposeMatching(([P:Exp|T:Exp] => P,T),([V:Val,Vs:Vals] => V,[Vs]))

/***********
  HIDDEN
***********/

  syntax K ::= #patternMatch(List{K}, List{K})   [function]
  rule #patternMatch(Ps:List{K}, Ks:List{K})
    => #patternMatch1(decomposeMatching(Ps,Ks), .Map)

  syntax K ::= #patternMatch1(List{K}, Map)  [function]
  rule #patternMatch1((decomposeMatching(X:Variable,K:K) => .List{K}),,_,
                      M:Map (.Map => X |-> K))
    when notBool $hasMapping(M,X)  // only linear patterns allowed for now
  rule #patternMatch1(.List{K}, M:Map) => #map(M)

endmodule
