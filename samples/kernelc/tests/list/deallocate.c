// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that deallocates a singly linked list.
 * In matchC, "." means "nothing"; technically, "." is the unit
 * of all collection structures (lists, sets, bags, maps, etc.).
 * By rewriting "list(x)(A)" into "." below, we mean that the list
 * that x points to disappears after the function is applied.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


void deallocate(struct listNode* x)
//@ rule <k> $ => return; ...</k> <heap>... list(x)(A) => . ...</heap>
{
  //@ inv <heap>... list(x)(?A) ...</heap>
  while(x != NULL) {
    struct listNode *y;

    y = x->next;
    free(x);
    x = y;
  }
}


//@ var A : Seq
