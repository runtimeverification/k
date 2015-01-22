// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "kernelc.k"

module AVL-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    find(tv(int, V:Int), tv(struct node *, TP:Pointer))
  =>
    tv(int, ?B:Int)
  ...</k>
  <heap>... htree(TP)(T:Tree) ...</heap>
requires avl(T)
ensures (?B =/=K 0) ==K (V inIntSet tree_keys(T))
endmodule

