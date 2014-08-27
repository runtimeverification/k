// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module HEAD-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k> head(tv(struct listNode *, LP:Pointer)) => tv(int, Y) ...</k>
  <heap>... list(LP)(Y:Int :: _:IntSeq) ...</heap>

endmodule
