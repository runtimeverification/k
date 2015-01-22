// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module TREE-TO-LIST-RECURSIVE-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    tree_to_list_recursive(tv(struct treeNode *, TP:Pointer), tv(struct listNode *, LP:Pointer))
  =>
    tv(struct listNode *, ?LP)
  ...</k>
  <heap>...
    tree(TP)(T:Tree) list(LP)(A:List)
  =>
    list(?LP:Pointer)(tree2inorder(T) A)
  ...</heap>
  <out>... .List => rev(tree2inorder(T)) </out>

endmodule
