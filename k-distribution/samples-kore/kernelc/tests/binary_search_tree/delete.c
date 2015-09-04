// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that deletes the node of the tree having a certain value and 
 * rebalances the tree to be a binary search tree.  Auxiliary function
 * find_min returns the leftmost leaf of a tree (holding its smallest element).
 */

#include <stdlib.h>

struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};

int find_min(struct treeNode *t)
{
  if (t->left == NULL)
    return t->value;
  else
    return find_min(t->left);
}

struct treeNode* delete(int v, struct treeNode *t)
{
  int min;

  if (t == NULL)
    return NULL;

  if (v == t->value) {
    if (t->left == NULL) {
      struct treeNode *temp;

      temp = t->right;
      free(t);

      return temp;
    }
    else if (t->right == NULL) {
      struct treeNode *temp;

      temp = t->left;
      free(t);

      return temp;
    }
    else {
      min = find_min(t->right);
      t->right = delete(min, t->right);
      t->value = min;
    }
  }
  else if (v < t->value)
    t->left = delete(v, t->left);
  else
    t->right = delete(v, t->right);

  return t;
}

