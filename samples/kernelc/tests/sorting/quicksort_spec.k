// Copyright (c) 2014 K Team. All Rights Reserved.
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
    (lseg(X, object(P1))(A:IntSeq)
     lseg(object(P1), null)(B:IntSeq)
     =>
     lseg(X, object(?P2))(?C:IntSeq)
     object(?P2) |-> (
          val  |-> tv(int, ?E:Int)
          next |-> tv(struct listNode *, null)))
  ...</heap>
ensures A @ B ==K ?C @ ([?E])

rule [append-func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    append(tv(struct listNode *, X:Pointer), tv(struct listNode *, Y:Pointer))
  =>
    tv(struct listNode *, ?P:Pointer)
  ...</k>
  <heap>...
    lseg(X, null)(A:IntSeq) lseg(Y, null)(B:IntSeq) => lseg(?P, null)(A @ B)
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
    (lseg(X, null)(A:IntSeq)
     lseg(Y1, null)(B1:IntSeq)
     lseg(Z1, null)(C1:IntSeq)
     =>
     lseg(?Y2, null)(?B2:IntSeq)
     lseg(?Z2, null)(?C2:IntSeq))
 ...</heap>
requires intseq2intset(B1) <=IntSet { V } andBool { V } <=IntSet intseq2intset(C1)
ensures intseq2intset(?B2) <=IntSet { V } andBool { V } <=IntSet intseq2intset(?C2)
  andBool intseq2intset(A) U intseq2intset(B1) U intseq2intset(C1) ==K intseq2intset(?B2) U intseq2intset(?C2)

rule [quicksort-func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    quicksort(tv(struct listNode *, X1:Pointer))
  =>
    tv(struct listNode *, ?X2:Pointer)
  ...</k>
  <heap>...
    lseg(X1, null)(A1:IntSeq) => lseg(?X2, null)(?A2:IntSeq)
  ...</heap>
ensures sorted(?A2) andBool intseq2intset(A1) ==K intseq2intset(?A2)
endmodule

