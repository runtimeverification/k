// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module REVERSE-SPEC
  imports KERNELC

rule [loop-inv1]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (x != NULL && x->val == v) {
      struct listNode* z;

      z = x->next;
      free(x);
      x = z;
    }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv(struct listNode * *, object(LX:Int))
    v |-> tv(int *, object(LV:Int))
  ...</env>
  <heap>...
    object(LX) |-> tv (struct listNode *, X1:Pointer => ?X2:Pointer)
    object(LV) |-> tv (int, V:Int)
    (lseg(X1, null)(A1:IntSeq)
     =>
     lseg(?X2, null)(?A2:IntSeq))
  ...</heap>
ensures filterIntSeq(V, A1) ==K filterIntSeq(V, ?A2)
  andBool (?A2 ==K [] orBool ?A2 ==K [V] @ ?A3:IntSeq)

/*
rule [loop-inv2]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while(y->next != NULL) {
      struct listNode* z;

      z = y->next;
      if(z->val == v) {
        y->next = z->next;
        free(z);
      }
      else
        y = z;
    }
  =>
    .K
  ...</k>
  <env>...
    x |-> tv(struct listNode * *, object(LX:Int))
    y |-> tv(struct listNode * *, object(LY:Int))
    v |-> tv(int *, object(LV:Int))
  ...</env>
  <heap>...
    object(LX) |-> tv (struct listNode *, X1:Pointer => ?X2:Pointer)
    object(LY) |-> tv (struct listNode *, X1:Pointer => ?X2:Pointer)
    object(LV) |-> tv (int, V:Int)
    (lseg(X1, null)(A1:IntSeq)
     =>
     lseg(?X2, null)(?A2:IntSeq))
  ...</heap>
ensures filterIntSeq(V, A1) ==K filterIntSeq(V, ?A2)
*/

/*
rule [func-spec]:
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
*/
endmodule

