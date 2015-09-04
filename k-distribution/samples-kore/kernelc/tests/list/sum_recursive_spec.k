// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module LENGTH-RECURSIVE-SPEC
  imports KERNELC

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    sum_recursive(tv(struct listNode *, LP:Pointer))
  =>
    tv(int, sum(A))
  ...</k>
  <heap>...
    list(LP)(A:List)
  ...</heap>

endmodule
