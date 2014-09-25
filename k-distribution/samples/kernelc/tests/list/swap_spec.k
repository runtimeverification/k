// Copyright (c) 2014 K Team. All Rights Reserved.
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
    lseg(LP, null)([V1:Int] @ [V2:Int] @ L:IntSeq)
  =>
    lseg(?LP, null)([V2] @ [V1] @ L)
  ...</heap>

endmodule
