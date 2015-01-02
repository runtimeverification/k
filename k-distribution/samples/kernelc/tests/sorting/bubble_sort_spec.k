// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module BUBBLE-SORT-SPEC
  imports KERNELC

rule [bubble-sort-loop-inv1]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (change) {
      struct listNode* y;

      change = 0;
      y = x;
      while (y->next != NULL) {
        if (y->val > y->next->val) {
          int temp;

          change = 1;
          temp = y->val;
          y->val = y->next->val;
          y->next->val = temp;
        }
        y = y->next;
      }
    }
  =>
    .K
  ...</k>
  // TODO: add back ... to the env cell when lookup and update for maps with
  // frames work better
  <env>
    x |-> tv(struct listNode * *, object(LX:Int))
    change |-> tv(int *, object(LC:Int))
  </env>
  <heap>...
    object(LX) |-> tv (struct listNode *, X:Pointer)
    object(LC) |-> tv (int, C:Int => ?_:Int)
    (lseg(X, null)(A1:List)
     =>
     lseg(X, null)(?A2:List))
 ...</heap>
requires X =/=K null andBool (sorted(A1) orBool C =/=K 0)
ensures sorted(?A2) andBool list2set(A1) ==K list2set(?A2)

rule [bubble-sort-loop-inv2]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (y->next != NULL) {
      if (y->val > y->next->val) {
        int temp;

        change = 1;
        temp = y->val;
        y->val = y->next->val;
        y->next->val = temp;
      }
      y = y->next;
    }
  =>
    .K
  ...</k>
  // TODO: add back ... to the env cell when lookup and update for maps with
  // frames work better
  <env>
    x |-> tv(struct listNode * *, object(LX:Int))
    y |-> tv(struct listNode * *, object(LY:Int))
    change |-> tv(int *, object(LC:Int))
  </env>
  <heap>...
    object(LX) |-> tv (struct listNode *, X:Pointer)
    object(LY) |-> tv (struct listNode *, object(Y1:Int) => object(?Y2:Int))
    object(LC) |-> tv (int, C1:Int => ?C2:Int)
    (object(Y1) |-> (
        val  |-> tv(int, V:Int)
        next |-> tv(struct listNode *, P:Pointer))
     lseg(X, object(Y1))(A1:List)
     lseg(P, null)(B:List)
     =>
     lseg(X, null)(?A2:List))
 ...</heap>
requires sorted(A1 ListItem(V)) orBool C1 =/=K 0
ensures (sorted(?A2) orBool ?C2 =/=K 0)
  andBool list2set(A1) U list2set(B) U { V } ==K list2set(?A2)

rule [bubble-sort-func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    bubble_sort(tv(struct listNode *, X1:Pointer))
  =>
    tv(struct listNode *, ?X2:Pointer)
  ...</k>
  <heap>...
    lseg(X1, null)(A1:List) => lseg(?X2, null)(?A2:List)
  ...</heap>
ensures sorted(?A2) andBool list2set(A1) ==K list2set(?A2)
  [trusted]
endmodule

