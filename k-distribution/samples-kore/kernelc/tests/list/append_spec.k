// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module APPEND-SPEC
  imports KERNELC

rule [loop-inv]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (p->next != NULL) {
      p = p->next;
    }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv(struct listNode * *, object(LX:Int))
    p |-> tv(struct listNode * *, object(LP:Int))
  ...</env>
  <heap>...
    object(LX) |-> tv (struct listNode *, X:Pointer)
    object(LP) |-> tv (struct listNode *, object(P1:Int) => object(?P2:Int))
    (lseg(X, object(P1))(A:List)
     lseg(object(P1), null)(B:List)
     =>
     lseg(X, object(?P2))(?C:List)
     object(?P2) |-> (
          val  |-> tv(int, ?E:Int)
          next |-> tv(struct listNode *, null)))
  ...</heap>
ensures A B ==K ?C ListItem(?E)

rule [func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    append(tv(struct listNode *, X:Pointer), tv(struct listNode *, Y:Pointer))
  =>
    tv(struct listNode *, ?P:Pointer)
  ...</k>
  <heap>...
    lseg(X, null)(A:List) lseg(Y, null)(B:List) => lseg(?P, null)(A B)
  ...</heap>
endmodule

