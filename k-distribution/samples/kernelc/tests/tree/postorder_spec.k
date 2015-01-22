// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module POSTORDER-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    postorder(tv(struct treeNode *, TP:Pointer))
  =>
    tv(void, undef)
  ...</k>
  <heap>...
    tree(TP)(T:Tree)
  ...</heap>
  <out>... .List => tree2postorder(T) </out>

endmodule
