require "k-equal.k"
require "int.k"


module LIST
  imports K-EQUAL-HOOKS
  imports INT-HOOKS

  syntax List ::= List List   [left, function, hook(List:__), klabel('_List_)]
                | ".List"       [function, hook(List:.List)]
                | ListItem(K)   [function, hook(List:ListItem)]

  /* element membership */
  syntax Bool ::= K "in" List   [function]
//  rule
//    K1:K in /* L1:List */ ListItem(K2:K) L2:List
//  =>
//    K1 =K K2 orBool /* K1 in L1 orBool */ K1 in L2
//  rule _ in .List => false

  /* list length */
  syntax Int ::= size(List)   [function]
//  rule
//    size(/* L1:List */ ListItem(_) L2:List)
//  =>
//    1 +Int /* size(L1) +Int */ size(L2)
//  rule size(.List) => 0
endmodule

