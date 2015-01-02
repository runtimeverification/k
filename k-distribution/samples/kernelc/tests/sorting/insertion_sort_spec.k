// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module INSERTION-SORT-SPEC
  imports KERNELC

rule [insertion-sort-loop-inv1]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (x != NULL) {
      struct listNode* n;

      n = x;
      x = x->next;
      n->next = NULL;
      if (y != NULL) {
        if (y->val < n->val) {
          struct listNode* z;

          z = y;
          while (z->next != NULL && z->next->val < n->val) {
            z = z->next;
          }

          n->next = z->next;
          z->next = n;
        }
        else {
          n->next = y;
          y = n;
        }
      }
      else {
        y = n;
      }
    }
  =>
    .K
  ...</k>
  // TODO: add back ... to the env cell when lookup and update for maps with
  // frames work better
  <env>
    x |-> tv(struct listNode * *, object(LX:Int))
    y |-> tv(struct listNode * *, object(LY:Int))
  </env>
  <heap>...
    object(LX) |-> tv (struct listNode *, X:Pointer => null)
    object(LY) |-> tv (struct listNode *, Y1:Pointer => ?Y2:Pointer)
    (lseg(Y1, null)(A1:List)
     lseg(X, null)(B:List)
     =>
     lseg(?Y2, null)(?A2:List))
 ...</heap>
requires sorted(A1)
ensures sorted(?A2) andBool list2set(A1) U list2set(B) ==K list2set(?A2)

rule [insertion-sort-loop-inv2]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (z->next != NULL && z->next->val < n->val) {
      z = z->next;
    }
    ~>
    n->next = z->next;
    z->next = n;
    .Statements
  =>
    .K
  ...</k>
  // TODO: add back ... to the env cell when lookup and update for maps with
  // frames work better
  <env>
    y |-> tv(struct listNode * *, object(LY:Int))
    z |-> tv(struct listNode * *, object(LZ:Int))
    n |-> tv(struct listNode * *, object(LN:Int))
    x |-> _
  </env>
  <heap>...
    object(LY) |-> tv(struct listNode *, Y:Pointer)
    object(LZ) |-> tv(struct listNode *, object(Z:Int) => ?_:Pointer)
    object(LN) |-> tv(struct listNode *, object(N:Int))
    (object(Z) |-> (
        val  |-> tv(int, V:Int)
        next |-> tv(struct listNode *, P:Pointer))
     object(N) |-> (
        val  |-> tv(int, NV:Int)
        next |-> tv(struct listNode *, null))
     lseg(Y, object(Z))(A1:List)
     lseg(P, null)(B:List)
     =>
     lseg(Y, null)(?A2:List))
 ...</heap>
requires sorted(A1 ListItem(V) B) andBool V <Int NV
ensures sorted(?A2)
  andBool list2set(A1) U list2set(B) U { V } U { NV } ==K list2set(?A2)

rule [insertion-sort-func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    insertion_sort(tv(struct listNode *, X1:Pointer))
  =>
    tv(struct listNode *, ?X2:Pointer)
  ...</k>
  <heap>...
    lseg(X1, null)(A1:List) => lseg(?X2, null)(?A2:List)
  ...</heap>
ensures sorted(?A2) andBool list2set(A1) ==K list2set(?A2)
endmodule

