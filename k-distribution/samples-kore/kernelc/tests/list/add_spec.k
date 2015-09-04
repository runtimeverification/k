// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module ADD-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    add(tv(int, V:Int), tv(struct listNode *, LP:Pointer))
  =>
    tv(struct listNode *, ?LP:Pointer)
  ...</k>
  <heap>... list(LP)(A:List) => list(?LP)(ListItem(V) A) ...</heap>

endmodule
