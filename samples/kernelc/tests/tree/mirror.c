// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function mirrors the structure of a binary tree.
 */


#include <stdlib.h>


struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};


void mirror(struct treeNode *t)
{
  struct treeNode *tmp;

  if (t == NULL)
    return;

  tmp = t->left;
  t->left = t->right;
  t->right = tmp;
  mirror(t->left);
  mirror(t->right);
}
