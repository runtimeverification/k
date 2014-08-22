// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that computes the height of a binary tree.
 */


#include <stdlib.h>


struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};


int max(int a, int b)
{
  return a > b ? a : b;
}

int height(struct treeNode *t)
{
  if (t == NULL) return 0;
  return 1 + max(height(t->left), height(t->right));
}
