// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that prints the contents of a binary tree in postorder traversal.
 */


#include <stdio.h>
#include <stdlib.h>


struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};


void postorder(struct treeNode *t)
{
  if (t == NULL)
    return;

  postorder(t->left);
  postorder(t->right);
  printf("%d ", t->value);
}
