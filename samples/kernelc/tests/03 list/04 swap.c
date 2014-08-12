/*
 * Function swapping the first two elements of a singly linked list.
 * The function specification requires that the list must have at
 * least two elements in order for the function to be called.
 */


#include <stdlib.h>
#include <stdio.h>


struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* swap(struct nodeList* x)
/*@ rule <k> $ => return ?x; ...</k> 
         <heap>... list(x)([v1, v2] @ A) => list(?x)([v2, v1] @ A) ...</heap> */
{
  struct nodeList* p;

  p = x;
  x = x->next;
  p->next = x->next;
  x->next = p;

  return x;
}

//@ var v : Int
//@ var A : Seq

