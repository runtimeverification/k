// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module QUICKSORT-SPEC
  imports KERNELC

rule [append-loop-inv]:
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

rule [append-func-spec]:
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

rule [quick-loop-inv]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while(x != NULL) {
      struct listNode* t;

      t = x;
      x = x->next;
      if (t->val < p->val) {
        t->next = y;
        y = t;
      }
      else {
        t->next = z;
        z = t;
      }
    }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv(struct listNode * *, object(LX:Int))
    p |-> tv(struct listNode * *, object(LP:Int))
    y |-> tv(struct listNode * *, object(LY:Int))
    z |-> tv(struct listNode * *, object(LZ:Int))
  ...</env>
  <heap>...
    object(LX) |-> tv (struct listNode *, X:Pointer => null)
    object(LP) |-> tv (struct listNode *, object(P:Int))
    object(LY) |-> tv (struct listNode *, Y1:Pointer => ?Y2:Pointer)
    object(LZ) |-> tv (struct listNode *, Z1:Pointer => ?Z2:Pointer)
    object(P) |-> (
        val  |-> tv(int, V:Int)
        next |-> tv(struct listNode *, null))
    (lseg(X, null)(A:List)
     lseg(Y1, null)(B1:List)
     lseg(Z1, null)(C1:List)
     =>
     lseg(?Y2, null)(?B2:List)
     lseg(?Z2, null)(?C2:List))
 ...</heap>
requires list2set(B1) <=IntSet { V } andBool { V } <=IntSet list2set(C1)
ensures list2set(?B2) <=IntSet { V } andBool { V } <=IntSet list2set(?C2)
  andBool list2set(A) U list2set(B1) U list2set(C1) ==K list2set(?B2) U list2set(?C2)

rule [quicksort-func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    quicksort(tv(struct listNode *, X1:Pointer))
  =>
    tv(struct listNode *, ?X2:Pointer)
  ...</k>
  <heap>...
    lseg(X1, null)(A1:List) => lseg(?X2, null)(?A2:List)
  ...</heap>
ensures sorted(?A2) andBool list2set(A1) ==K list2set(?A2)
endmodule

