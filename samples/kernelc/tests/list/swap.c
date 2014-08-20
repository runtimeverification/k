// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function swapping the first two elements of a singly linked list.
 * The function specification requires that the list must have at
 * least two elements in order for the function to be called.
 */


#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* swap(struct listNode* x)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)([v1, v2] @ A) => list(?x)([v2, v1] @ A) ...</heap> */
{
  struct listNode* p;

  p = x;
  x = x->next;
  p->next = x->next;
  x->next = p;

  return x;
}

//@ var v : Int
//@ var A : Seq
