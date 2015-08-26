// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function reverse reverses in-place the nodes of a singly linked list.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* reverse(struct listNode *x)
/*@ rule <k> $ => return ?p; ...</k>
         <heap>... list(x)(A) => list(?p)(rev(A)) ...</heap> */
{
  struct listNode *p;

  p = NULL;
  //@ inv <heap>... list(p)(?B), list(x)(?C) ...</heap> /\ A = rev(?B) @ ?C
  while(x != NULL) {
    struct listNode *y;

    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }

  return p;
}


//@ var A, B, C : Seq
