// Copyright (c) 2014 K Team. All Rights Reserved.
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
    x |-> tv (struct listNode * * , object(P1:Int))
    s |-> tv (int *, object(P2:Int))
  ...</env>
  <heap>...
    object(P1) |-> tv (struct listNode *, LP:Pointer => null)
    object(P2) |-> tv (int, S:Int => S +Int sum(A))
    list(LP)(A:IntSeq)
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
    list(LP)(A:IntSeq)
  ...</heap>

endmodule
