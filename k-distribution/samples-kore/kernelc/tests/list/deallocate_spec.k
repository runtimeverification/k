// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module DEALLOCATE-SPEC
  imports KERNELC

rule [loop-inv]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while(x != NULL) {
      struct listNode *y;

      y = x->next;
      free(x);
      x = y;
    }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv(struct listNode * *, object(LX:Int))
  ...</env>
  <heap>...
    object(LX) |-> tv (struct listNode *, LP:Pointer => null)
    (list(LP)(_:List) => .Map)
  ...</heap>

rule [func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    deallocate(tv(struct listNode *, LP:Pointer))
  =>
    tv(void, undef)
  ...</k>
  <heap>...
    list(LP)(_:List) => .Map
  ...</heap>

endmodule
