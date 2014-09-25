// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that searches an avl tree for a node with a certain value. It is
 * almost identical to the find function of binary search trees. The fact that
 * the tree is an avl does not matter in this case.
 */

#include<stdlib.h>

struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};

int find(int v, struct node *t)
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

