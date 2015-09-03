// Copyright (c) 2014-2015 K Team. All Rights Reserved.
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
    x |-> tv (struct listNode * * , object(LX:Int))
    y |-> tv (int *, object(LY:Int))
  ...</env>
  <heap>...
    object(LX) |-> tv (struct listNode *, LP:Pointer => null)
    object(LY) |-> tv (int, L:Int => L +Int size(A))
    list(LP)(A:List)
  ...</heap>

rule [func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    length_iterative(tv(struct listNode *, LP:Pointer))
  =>
    tv(int, size(A))
  ...</k>
  <heap>...
    list(LP)(A:List)
  ...</heap>

endmodule
