// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "k-prelude.k"

module SUBSTITUTION
  imports MAP

  syntax Variable //sort declaration used by substitution hook

  syntax K ::= K "[" K "/" K "]"  [function, hook(SUBSTITUTION.userSubstitution), impure]
  syntax K ::= K "[" Map "]" [function]
  syntax Set ::= freeVariables(KList)  [function, hook(Substitution:freeVariables), latex({\it FV}({#1})), impure]
  syntax K ::= freshVariables(Set, K) [function, hook(MetaK:freshVariables), impure]

  rule K:K [ K1 |-> K2 M:Map ] => K [ K2 / K1 ] [ M ]
  rule K:K [ .Map ] => K

endmodule
