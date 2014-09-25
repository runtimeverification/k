// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that inserts a new value into a binary search tree.
 */

#include <stdlib.h>

struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};


struct treeNode* new_node(int v)
{
  struct treeNode *node;
  node = (struct treeNode *) malloc(sizeof(struct treeNode));
  node->value = v;
  node->left = NULL;
  node->right = NULL;
  return node;
}


struct treeNode* insert(int v, struct treeNode *t)
{
  if (t == NULL)
    return new_node(v);

  if (v < t->value)
    t->left = insert(v, t->left);
  else if (v > t->value) 
    t->right = insert(v, t->right);

  return t;
}

