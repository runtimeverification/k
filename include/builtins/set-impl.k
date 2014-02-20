require "set.k"


module SET-IMPL
  imports SET

  /* set difference */
//  syntax Set ::= Set "-Set" Set   [function, hook(Set:difference), latex({#1}-_{\it Set}{#2})]
  rule (SetItem(K:K) S1:Set) -Set S2:Set => S1 -Set S2
  when K in S2
  rule (SetItem(K:K) S1:Set) -Set S2:Set => SetItem(K) (S1 -Set S2)
  when notBool(K in S2)
  rule .Set -Set _:Set => .Set

  /* set difference axioms */
  rule S1:Set -Set (SetItem(K:K) S2:Set) => S1 -Set S2
  when notBool(K in S1)
  rule S:Set -Set .Set => S

  /* set intersection */
//  syntax Set ::= intersectSet(Set, Set)   [function]
  rule intersectSet(S1:Set, S2:Set) => S1 -Set (S1 -Set S2)

  /* element membership */
//  syntax Bool ::= K "in" Set    [function, hook(Set:in)]
  rule K1:K in SetItem(K2:K) S:Set => K1 =K K2 orBool K1 in S
  rule _ in .Set => false

  /* set cardinality */
//  syntax Int ::= size(Set)   [function]
  rule size(SetItem(_) S:Set) => 1 +Int size(S)
  rule size(.Set) => 0
endmodule

