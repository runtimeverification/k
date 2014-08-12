/*
 * Function length_recursive returns the length of a singly linked list.
 * The length is recursively computed.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


int length_recursive(struct listNode* x)
//@ rule <k> $ => return len(A); ...</k> <heap>... list(x)(A) ...</heap>
{
  if (x == 0)
    return 0;

  return 1 + length_recursive(x->next);  
}


//@ var A : Seq

