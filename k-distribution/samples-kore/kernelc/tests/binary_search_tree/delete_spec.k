// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "kernelc.k"

module BST-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    delete(tv(int, V:Int), tv(struct treeNode *, TP1:Pointer))
  =>
    tv(struct treeNode *, ?TP2:Pointer)
  ...</k>
  <heap>... tree(TP1)(T1:Tree) => tree(?TP2)(?T2:Tree) ...</heap>
requires bst(T1)
ensures bst(?T2) andBool tree_keys(?T2) ==K tree_keys(T1) -IntSet { V }

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    find_min(tv(struct treeNode *, TP:Pointer))
  =>
    tv(int, ?M:Int)
  ...</k>
  <heap>... tree(TP)(T:Tree) ...</heap>
requires TP =/=K null andBool bst(T)
ensures (?M inIntSet tree_keys(T)) andBool ({ ?M } <=IntSet tree_keys(T))
endmodule

