// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module MIRROR-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    mirror(tv(struct treeNode *, TP:Pointer))
  =>
    tv(void, undef)
  ...</k>
  <heap>...
    tree(TP)(T:Tree => tree_mirror(T))
  ...</heap>

endmodule
