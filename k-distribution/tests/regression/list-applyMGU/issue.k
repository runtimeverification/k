// Copyright (c) 2014 K Team. All Rights Reserved.
require "modules/unification.k"

module ISSUE
  imports UNIFICATION
  syntax KItem ::= "a" | "b"
  syntax Variable ::= "x"
  configuration <k> a ~> b </k>
                <list> ListItem(x) </list> <set> SetItem(x) </set>
                <mgu> updateMgu(.Mgu, x, "success") </mgu>
                <out stream="stdout"> .List </out>

  rule <k> a => . ...</k>
       <list> L:List => applyMgu(Theta:K, L) </list>
       <set> S:Set => applyMgu(Theta:K, S) </set>
       <mgu> Theta:K </mgu>

  rule <k> b => . ...</k>
       <list> ListItem("success") </list>
       <set> SetItem("success") </set>
       <out>... .List => ListItem("success") </out>
endmodule

