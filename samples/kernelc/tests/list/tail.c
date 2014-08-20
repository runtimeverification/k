// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function tail returns the tail of a singly linked list. The
 * specification requires the list to have at least one element.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* tail(struct listNode *x)
/*@ rule <k> $ => return n; ...</k>
         <heap>... x |-> [v, n], list(n)(A) ...</heap> */
{
  return x->next;
}


//@ var v, n : Int
//@ var A : Seq
