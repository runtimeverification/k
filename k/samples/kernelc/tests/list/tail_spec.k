// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module TAIL-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    tail(tv(struct listNode *, LP:Pointer))
  =>
    tv(struct listNode *, Tail:Pointer)
  ...</k>
  <heap>...
    LP |-> (
      val  |-> tv(int, _:Int)
      next |-> tv(struct listNode *, Tail)
    )
    list(Tail)(L:IntSeq)
  ...</heap>

endmodule
