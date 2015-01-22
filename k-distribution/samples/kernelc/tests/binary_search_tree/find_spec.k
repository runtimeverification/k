// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "kernelc.k"

module BST-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    find(tv(int, V:Int), tv(struct treeNode *, TP:Pointer))
  =>
    tv(int, ?B:Int)
  ...</k>
  <heap>... tree(TP)(T:Tree) ...</heap>
requires bst(T)
ensures (?B =/=K 0) ==K (V inIntSet tree_keys(T))
endmodule

