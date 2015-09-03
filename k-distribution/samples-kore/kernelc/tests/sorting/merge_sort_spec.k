// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module MERGESORT-SPEC
  imports KERNELC

rule [mergesort-loop-inv1]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (x != NULL) {
      struct listNode* t;

      t = x;
      x = x->next;
      t->next = y;
      y = t;

      if (x != NULL) {
        t = x;
        x = x->next;
        t->next = z;
        z = t;
      }
    }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv(struct listNode * *, object(LX:Int))
    y |-> tv(struct listNode * *, object(LY:Int))
    z |-> tv(struct listNode * *, object(LZ:Int))
  ...</env>
  <heap>...
    object(LX) |-> tv (struct listNode *, X:Pointer => null)
    object(LY) |-> tv (struct listNode *, object(Y1:Int) => object(?Y2:Int))
    object(LZ) |-> tv (struct listNode *, object(Z1:Int) => object(?Z2:Int))
    (lseg(X, null)(A:List)
     lseg(object(Y1), null)(B1:List)
     lseg(object(Z1), null)(C1:List)
     =>
     lseg(object(?Y2), null)(?B2:List)
     lseg(object(?Z2), null)(?C2:List))
 ...</heap>
ensures list2set(A) U list2set(B1) U list2set(C1) ==K list2set(?B2) U list2set(?C2)

rule [mergesort-loop-inv2]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (y != NULL && z != NULL) {
      if (y->val < z->val) {
        p->next = y;
        y = y->next;
      }
      else {
        p->next = z;
        z = z->next;
      }

      p = p->next;
    }
    ~>
    if (y != NULL)
      p->next = y;
    else
      p->next = z;
    S:Statement Ss:Statements
  =>
    S Ss
  ...</k>
  <env>...
    x |-> tv(struct listNode * *, object(LX:Int))
    y |-> tv(struct listNode * *, object(LY:Int))
    z |-> tv(struct listNode * *, object(LZ:Int))
    p |-> tv(struct listNode * *, object(LP:Int))
  ...</env>
  <heap>...
    object(LX) |-> tv (struct listNode *, X:Pointer)
    object(LY) |-> tv (struct listNode *, Y:Pointer => ?_:Pointer)
    object(LZ) |-> tv (struct listNode *, Z:Pointer => ?_:Pointer)
    object(LP) |-> tv (struct listNode *, object(P:Int) => ?_:Pointer)
    (object(P) |-> (
        val  |-> tv(int, V:Int)
        next |-> tv(struct listNode *, _:Pointer))
     lseg(X, object(P))(A1:List)
     lseg(Y, null)(B:List)
     lseg(Z, null)(C:List)
     =>
     lseg(X, null)(?A2:List))
 ...</heap>
requires sorted(A1 ListItem(V)) andBool sorted(B) andBool sorted(C)
  andBool list2set(A1) U {V} <=IntSet list2set(B) U list2set(C)
ensures sorted(?A2)
  andBool list2set(A1) U list2set(B) U list2set(C) U { V } ==K list2set(?A2)

rule [mergesort-func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    merge_sort(tv(struct listNode *, X1:Pointer))
  =>
    tv(struct listNode *, ?X2:Pointer)
  ...</k>
  <heap>...
    lseg(X1, null)(A1:List) => lseg(?X2, null)(?A2:List)
  ...</heap>
ensures sorted(?A2) andBool list2set(A1) ==K list2set(?A2)
endmodule

