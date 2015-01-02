// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module COPY-SPEC
  imports KERNELC

rule [loop-inv]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while(iterx) {
      struct listNode *node;

      node = (struct listNode *) malloc(sizeof(struct listNode));
      node->val = iterx->val;
      node->next = NULL;
      itery->next = node;
      iterx = iterx->next;
      itery = itery->next;
      //breakpoint
    }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv(struct listNode * *, object(LX:Int))
    y |-> tv(struct listNode * *, object(LY:Int))
    iterx |-> tv(struct listNode * *, object(LIX:Int))
    itery |-> tv(struct listNode * *, object(LIY:Int))
  ...</env>
  <heap>...
    object(LX) |-> tv (struct listNode *, X:Pointer)
    object(LY) |-> tv (struct listNode *, Y:Pointer)
    object(LIX) |-> tv (struct listNode *, IX:Pointer => ?_:Pointer)
    object(LIY) |-> tv (struct listNode *, object(IY:Int) => ?_:Pointer)
    (lseg(X, IX)(A:List ListItem(V:Int))
     lseg(IX, null)(B:List)
     lseg(Y, object(IY))(A)
     object(IY) |-> (
          val  |-> tv(int, V)
          next |-> tv(struct listNode *, null))
     =>
     lseg(X, null)(A ListItem(V) B)
     lseg(Y, null)(A ListItem(V) B))
  ...</heap>

rule [func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    copy(tv(struct listNode *, X:Pointer))
  =>
    tv(struct listNode *, ?Y:Pointer)
  ...</k>
  <heap>... lseg(X, null)(A:List) (.Map  => lseg(?Y, null)(A)) ...</heap>
endmodule

