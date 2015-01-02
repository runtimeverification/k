// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module SWAP-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    swap(tv(struct listNode *, LP:Pointer))
  =>
    tv(struct listNode *, ?LP:Pointer)
  ...</k>
  <heap>...
    lseg(LP, null)(ListItem(V1:Int) ListItem(V2:Int) L:List)
  =>
    lseg(?LP, null)(ListItem(V2) ListItem(V1) L)
  ...</heap>

endmodule
