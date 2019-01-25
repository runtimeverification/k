// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module INORDER-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    inorder(tv(struct treeNode *, TP:Pointer))
  =>
    tv(void, undef)
  ...</k>
  <heap>...
    tree(TP)(T:Tree)
  ...</heap>
  <out>... .List => tree2inorder(T) </out>
endmodule
