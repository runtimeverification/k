// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function sum_iterative  returns the sum of the elements of a
 * singly linked list. The sum is iteratively computed.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


int sum_iterative(struct listNode* x)
//@ rule <k> $ => return sum(A); ...</k> <heap>... list(x)(A) ...</heap>
{
  int s;

  s = 0;
  /*@ inv <heap>... lseg(old(x), x)(?A1), list(x)(?A2) ...</heap>
          /\ A = ?A1 @ ?A2 /\ s = sum(?A1) */
  while (x != NULL) {
    s = s + x->val;
    x = x->next;
  }

  return s;
}


/*@ var A : Seq */
