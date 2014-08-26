// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module PREORDER-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    preorder(tv(struct treeNode *, TP:Pointer))
  =>
    tv(void, undef)
  ...</k>
  <heap>...
    tree(TP)(T:Tree)
  ...</heap>
  <out>... .List => intseq2list(tree2preorder(T)) </out>

endmodule
