// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function add prepends an integer value to the beginning of a singly
 * linked list.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* add(int v, struct listNode* x)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A) => list(?x)([v] @ A) ...</heap> */
{
  struct listNode* y;

  y = (struct listNode*) malloc (sizeof(struct listNode));
  y->val = v;
  y->next = x;

  return y;
}


//@ var A : Seq
