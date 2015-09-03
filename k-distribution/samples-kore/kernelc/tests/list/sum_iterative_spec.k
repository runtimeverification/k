// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module SUM-ITERATIVE-SPEC
  imports KERNELC

rule [loop-inv]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (x != NULL) {
      s = s + x->val;
      x = x->next;
    }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv (struct listNode * * , object(LX:Int))
    s |-> tv (int *, object(LS:Int))
  ...</env>
  <heap>...
    object(LX) |-> tv (struct listNode *, LP:Pointer => null)
    object(LS) |-> tv (int, S:Int => S +Int sum(A))
    list(LP)(A:List)
  ...</heap>

rule [func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    sum_iterative(tv(struct listNode *, LP:Pointer))
  =>
    tv(int, sum(A))
  ...</k>
  <heap>...
    list(LP)(A:List)
  ...</heap>

endmodule
