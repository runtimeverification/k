// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function append concatenates two singly linked lists and returns the
 * first element of the resulting list.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* append(struct listNode *x, struct listNode *y)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A), list(y)(B) => list(?x)(A @ B) ...</heap> */
{
  struct listNode *p;
  if (x == NULL)
    return y;

  p = x;
  /*@ inv <heap>... lseg(x, p)(?A1), list(p)(?A2) ...</heap>
          /\ A = ?A1 @ ?A2 /\ ~(p = 0) */
  while (p->next != NULL)
    p = p->next;
  p->next = y;

  return x;
}


//@ var A, B : Seq
