// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module LENGTH-ITERATIVE-SPEC
  imports KERNELC

rule [loop-inv]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (x != NULL) {
      y = y + 1;
      x = x->next;
    }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv (struct listNode * * , object(P1:Int))
    y |-> tv (int *, object(P2:Int))
  ...</env>
  <heap>...
    object(P1) |-> tv (struct listNode *, LP:Pointer => null)
    object(P2) |-> tv (int, L:Int => L +Int len(A))
    list(LP)(A:IntSeq)
  ...</heap>

rule [func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    length_iterative(tv(struct listNode *, LP:Pointer))
  =>
    tv(int, len(A))
  ...</k>
  <heap>...
    list(LP)(A:IntSeq)
  ...</heap>

endmodule
