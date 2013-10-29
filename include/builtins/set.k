require "k-equal.k"
require "int.k"


module SET
  imports K-EQUAL-HOOKS
  imports INT-HOOKS

  syntax MySet ::= MySet MySet    [left, function, hook(Set:__), klabel('_Set_)]
                 | ".MySet"       [function, hook(Set:.Set)]
                 | MySetItem(K)   [function, hook(Set:SetItem)]

  /* set difference */
  syntax MySet ::= MySet "-MySet" MySet   [function, hook(Set:difference), latex({#1}-_{\it Set}{#2})]
  rule (MySetItem(K:K) S1:MySet) -MySet S2:MySet => S1 -MySet S2
  when K in S2
  rule (MySetItem(K:K) S1:MySet) -MySet S2:MySet => MySetItem(K) (S1 -MySet S2)
  when notBool(K in S2)
  rule .MySet -MySet _:MySet => .MySet

  /* set difference axioms */
  rule S1:MySet -MySet (MySetItem(K:K) S2:MySet) => S1 -MySet S2
  when notBool(K in S1)
  rule S:MySet -MySet .MySet => S

  /* set intersection */
  syntax MySet ::= intersectSet(MySet, MySet)   [function]
  rule intersectSet(S1:MySet, S2:MySet) => S1 -MySet (S1 -MySet S2)

  /* element membership */
  syntax Bool ::= K "in" MySet    [function, hook(Set:in)]
  rule K1:K in MySetItem(K2:K) S:MySet => K1 =K K2 orBool K1 in S
  rule _ in .MySet => false

  /* set cardinality */
  syntax Int ::= size(MySet)   [function]
  rule size(MySetItem(_) S:MySet) => 1 +Int size(S)
  rule size(.MySet) => 0
endmodule

