// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module REVERSE-SPEC
  imports KERNELC

rule [loop-inv]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    // if (x != NULL) { // TODO(YilongL): this rule is still provable after changing `while` to `if` (note that `LP1:Pointer => null`); is it a bug in ConstrainedTerm#matchImplies?
    while (x != NULL) {
      struct listNode *y;

      y = x->next;
      x->next = p;
      p = x;
      x = y;
    }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv(struct listNode * *, object(P1:Int))
    p |-> tv(struct listNode * *, object(P2:Int))
  ...</env>
  <heap>...
    object(P1) |-> tv (struct listNode *, LP1:Pointer => null)
    object(P2) |-> tv (struct listNode *, LP2:Pointer => ?LP2:Pointer)
    (list(LP1)(B:IntSeq) list(LP2)(C:IntSeq) => list(?LP2)(?A:IntSeq))
  ...</heap>
ensures ?A ==K rev(B) @ C

rule [func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    reverse(tv(struct listNode *, LP:Pointer))
  =>
    tv(struct listNode *, ?LP:Pointer)
  ...</k>
  <heap>...
    list(LP)(A:IntSeq) => list(?LP)(rev(A))
  ...</heap>

endmodule
