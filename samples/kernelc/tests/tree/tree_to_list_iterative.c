// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that iteratively transforms a binary tree into a singly linked list,
 * at the same time printing the list of elements in reverse order.
 */


#include <stdlib.h>
#include <stdio.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};

struct listNode {
  int val;
  struct listNode *next;
};

struct stackNode {
  struct treeNode *val;
  struct stackNode *next;
};


struct listNode* tree_to_list_iterative(struct treeNode *t)
/*@ rule <k> $ => return ?l; ...</k>
         <heap>... tree(t)(T) => list(?l)(tree2list(T)) ...</heap>
         <out>... . => rev(tree2list(T)) </out> */
{
  struct listNode *l;
  struct stackNode *s;

  if (t == NULL)
    return NULL;

  l = NULL;
  s = (struct stackNode *) malloc(sizeof(struct stackNode));
  s->val = t;
  s->next = NULL;
  /*@ inv <heap>... treeList(s)(?TS), list(l)(?A) ...</heap>
          <out>... rev(?A) </out>
          /\ tree2list(T) = treeList2list(rev(?TS)) @ ?A */
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
      ln->val = tn->val;
      ln->next = l;
      l = ln;
      printf("%d ", ln->val);
      free(tn);
    }
  }

  return l;
}


//@ var A, TS : Seq
//@ var T : Tree
