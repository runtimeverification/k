// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module TREE-TO-LIST-ITERATIVE-SPEC
  imports KERNELC

rule [loop-inv]:
  <struct>... STRUCT:Map ...</struct>
  <k>
    while (s != NULL) {
      struct treeNode *tn;
      struct listNode *ln;
      struct stackNode *sn;

      sn = s;
      s = s->next ;
      tn = sn->val;
      free(sn) ;
      if (tn->left != NULL) {
        sn = (struct stackNode *) malloc(sizeof(struct stackNode));
        sn->val = tn->left;
        sn->next = s;
        s = sn;
      }
      if (tn->right != NULL) {
        sn = (struct stackNode *) malloc(sizeof(struct stackNode));
        sn->val = tn;
        sn->next = s;
        s = sn;
        sn = (struct stackNode *) malloc(sizeof(struct stackNode));
        sn->val = tn->right;
        sn->next = s;
        s = sn;
        tn->left = NULL;
        tn->right = NULL;
      }
      else {
        ln = (struct listNode *) malloc(sizeof(struct listNode));
        ln->val = tn->value;
        ln->next = l;
        l = ln;
        printf("%d ", ln->val);
        free(tn);
      }
    }
  =>
    .K
  ...</k>
  <env>...
    l |-> tv(struct listNode * *, object(P1:Int))
    s |-> tv(struct stackNode * *, object(P2:Int))
  ...</env>
  <heap>...
    object(P1) |-> tv(struct listNode *, LP:Pointer => ?LP:Pointer)
    object(P2) |-> tv(struct stackNode *, SP:Pointer => null)
    (treeList(SP)(TS:TreeSeq) list(LP)(A:List)
      =>
    list(?LP)(treeseq2intseq(TS) A))
  ...</heap>
  <out>... .List => rev(treeseq2intseq(TS)) </out>

rule [func-spec]:
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    tree_to_list_iterative(tv(struct treeNode *, TP:Pointer))
  =>
    tv(struct listNode *, ?LP)
  ...</k>
  <heap>...
    tree(TP)(T:Tree)
  =>
    list(?LP:Pointer)(tree2inorder(T))
  ...</heap>
  <out>... .List => rev(tree2inorder(T)) </out>

endmodule
