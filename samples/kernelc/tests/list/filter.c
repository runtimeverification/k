// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function filter deletes the nodes of a singly linked list that hold
 * the value "v".
 */


#include<stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* filter(int v, struct listNode* x)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A) => list(?x)(filter(v, A)) ...</heap> */
{
  struct listNode* y;

  // Variable !v below stays unchanged during loop iterations,
  // so "v = !v" says that the value of v is not changed by the loop.
  //@ inv <heap>...list(x)(?A)...</heap> /\ v = !v /\ filter(v,A) = filter(v,?A)
  while (x != NULL && x->val == v) {
    struct listNode* z;

    z = x->next;
    free(x);
    x = z;
  }

  if (x == NULL)
    return NULL;

  y = x;
  /*@ inv <heap>... lseg(x, y)(?B), y |-> [?v, ?n], list(?n)(?C) ...</heap>
          /\ v = !v /\ filter(v, A) = ?B @ [?v] @ filter(v, ?C) */
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

  return x;
}


/*@ var n : Int */
/*@ var A, B, C : Seq */
