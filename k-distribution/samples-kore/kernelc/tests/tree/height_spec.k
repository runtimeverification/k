// Copyright (c) 2014-2018 K Team. All Rights Reserved.
module HEIGHT-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    height(tv(struct treeNode *, TP:Pointer))
  =>
    tv(int, tree_height(T))
  ...</k>
  <heap>...
    tree(TP)(T:Tree)
  ...</heap>
endmodule
