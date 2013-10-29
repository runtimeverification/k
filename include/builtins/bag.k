require "k-equal.k"
require "int.k"


module BAG
  imports K-EQUAL-HOOKS
  imports INT-HOOKS

  syntax MyBag ::= MyBag MyBag    [function, hook(Bag:__), klabel('_Bag_)]
                 | ".MyBag"       [function, hook(Bag:.Bag)]
                 | MyBagItem(K)   [function, hook(Bag:BagItem)]

  /* element membership */
  syntax Bool ::= K "in" MyBag    [function]
  rule K1 in MyBagItem(K2) B:MyBag => (K1 =K K2) orBool (K1 in B)
  rule _ in .MyBag => false

  /* set cardinality */
  syntax Int ::= size(MyBag)   [function]
  rule size(MyBagItem(_) B:MyBag) => 1 +Int size(B)
  rule size(.MyBag) => 0
endmodule
