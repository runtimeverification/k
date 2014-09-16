// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that prints the contents of a binary tree in preorder traversal.
 */


#include <stdio.h>
#include <stdlib.h>


struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};


void preorder(struct treeNode *t)
{
  if (t == NULL)
    return;

  printf("%d ", t->value);
  preorder(t->left);
  preorder(t->right);
}
