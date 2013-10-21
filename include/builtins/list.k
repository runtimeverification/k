require "k-equal.k"
require "int.k"


module LIST
  imports K-EQUAL-HOOKS
  imports INT-HOOKS

  syntax MyList ::= MyList MyList   [left, function, hook(List:__), klabel('_List_)]
                  | ".MyList"       [function, hook(List:.List)]
                  | MyListItem(K)   [function, hook(List:ListItem)]

  /* element membership */
  syntax Bool ::= K "in" MyList   [function]
  rule
    K1:K in /* L1:MyList */ MyListItem(K2:K) L2:MyList
  =>
    K1 =K K2 orBool /* K1 in L1 orBool */ K1 in L2
  rule _ in .MyList => false

  /* list length */
  syntax Int ::= size(MyList)   [function]
  rule
    size(/* L1:MyList */ MyListItem(_) L2:MyList)
  =>
    1 +Int /* size(L1) +Int */ size(L2)
  rule size(.MyList) => 0
endmodule

