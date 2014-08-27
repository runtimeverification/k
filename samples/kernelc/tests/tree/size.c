// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that computes the number of nodes of a binary tree without
 * altering its content.
 */


#include <stdlib.h>


struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};


int compute_size(struct treeNode *t)
{
  if (t == NULL) return 0;
  return 1 + compute_size(t->left) + compute_size(t->right);
}
