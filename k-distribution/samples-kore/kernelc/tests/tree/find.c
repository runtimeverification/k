// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that searches a binary tree for a node with a certain value.
 */


#include <stdlib.h>


struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};


int find(int v, struct treeNode *t)
/*@ rule <k> $ => return r; ...</k> <heap>... tree(t)(T) ...</heap>
    if (~(r = 0) <==> in(v, tree2mset(T))) */
{
  if (t == NULL)
    return 0;

  return v == t->value || find(v, t->left) || find(v, t->right);
}


//@ var r : Int
//@ var T : Tree
