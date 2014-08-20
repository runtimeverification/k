// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function copy duplicates a singly linked list by allocating memory and
 * copying the content of the original list to the newly created one.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* copy(struct listNode *x)
/*@ rule <k> $ => return ?y; ...</k>
         <heap>... list(x)(A), (. => list(?y)(A)) ...</heap> */
{
  struct listNode *y;
  struct listNode *iterx;
  struct listNode *itery;

  if (x == NULL)
    return NULL;

  y = (struct listNode *) malloc(sizeof(struct listNode));
  y->val = x->val;
  y->next = NULL;

  iterx = x->next;
  itery = y;
  /*@ inv <heap>... lseg(old(x), iterx)(?B @ [?v]), list(iterx)(?C),
                    lseg(y, itery)(?B), itery |-> [?v, 0] ...</heap>
          /\ A = ?B @ [?v] @ ?C */
  while(iterx) {
    struct listNode *node;

    node = (struct listNode *) malloc(sizeof(struct listNode));
    node->val = iterx->val;
    node->next = NULL;
    itery->next = node;
    iterx = iterx->next;
    itery = itery->next;
  }

  return y;
}


/*@ var v: Int */
/*@ var A, B, C : Seq */
