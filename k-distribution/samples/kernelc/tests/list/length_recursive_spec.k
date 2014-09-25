// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module LENGTH-RECURSIVE-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    length_recursive(tv(struct listNode *, LP:Pointer))
  =>
    tv(int, len(A))
  ...</k>
  <heap>...
    list(LP)(A:IntSeq)
  ...</heap>

endmodule
