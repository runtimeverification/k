// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that prints the contents of a binary tree in inorder traversal.
 */


#include <stdio.h>
#include <stdlib.h>


struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};


void inorder(struct treeNode *t)
{
  if (t == NULL)
    return;

  inorder(t->left);
  printf("%d ", t->value);
  inorder(t->right);
}
