// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Program that traverses a list of disjoint trees and deallocates each tree.
 * The heap pattern tlist specifies the existence of a list of disjoint trees
 * in the heap.
 */


#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};

struct listNode {
  struct treeNode *val;
  struct listNode *next;
};


void deallocate(struct treeNode *t)
//@ rule <k> $ => return; ...</k> <heap>... tree(t)(T) => . ...</heap>
{
  if (t == NULL)
    return;

  deallocate(t->left);
  deallocate(t->right);
  free(t);
}

void iter_deallocate(struct listNode *l)
/*@ rule <k> $ => return; ...</k>
         <heap>... tlist(l)(TS) => list(l)(A) ...</heap> */
{
  //@ inv <heap>... lseg(old(l), l)(?A), tlist(l)(?TS) ...</heap>
  while (l != NULL) {
    deallocate(l->val);
    l = l->next;
  }
}


//@ var A, TS : Seq
//@ var T : Tree
