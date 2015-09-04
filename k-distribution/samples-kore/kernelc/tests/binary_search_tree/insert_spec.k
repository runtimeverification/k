// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "kernelc.k"

module BST-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    insert(tv(int, V:Int), tv(struct treeNode *, TP1:Pointer))
  =>
    tv(struct treeNode *, ?TP2:Pointer)
  ...</k>
  <heap>... tree(TP1)(T1:Tree) => tree(?TP2)(?T2:Tree) ...</heap>
requires bst(T1)
ensures bst(?T2) andBool tree_keys(?T2) ==K { V } U tree_keys(T1)
endmodule

