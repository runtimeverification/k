// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module SIZE-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    compute_size(tv(struct treeNode *, TP:Pointer))
  =>
    tv(int, tree_size(T))
  ...</k>
  <heap>...
    tree(TP)(T:Tree)
  ...</heap>
endmodule
