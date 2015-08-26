// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that searches a binary search tree for a node with a certain value.
 */
#include <stdlib.h>

struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};

int find(int v, struct treeNode *t)
{
  if (t == NULL)
    return 0;
  else if (v == t->value)
    return 1;
  else if (v < t->value)
    return find(v, t->left);
  else
    return find(v, t->right);
}

