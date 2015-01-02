// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "list.k"

module LIST-IMPL
  imports LIST
  imports BOOL-HOOKS
  imports INT-HOOKS

  // syntax Bool ::= K "in" List
  rule K:K in ListItem(K) _:List => true
  rule K1:K in ListItem(K2:K) L:List => K1 =K K2 orBool K1 in L
  rule _ in .List => false

  // syntax Int ::= size(List)
  rule size(ListItem(_) L:List) => 1 +Int size(L)
  rule size(.List) => 0
endmodule

