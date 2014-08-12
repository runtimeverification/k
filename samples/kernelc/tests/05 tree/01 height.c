/*
 * Function that computes the height of a binary tree.
 */


#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


int max(int a, int b)
{
  return a > b ? a : b;
}

int tree_height(struct treeNode *t)
//@ rule <k> $ => return height(T); ...</k> <heap>... tree(t)(T) ...</heap>
{
  if (t == NULL) return 0;
  return 1 + max(tree_height(t->left), tree_height(t->right));
}


//@ var T : Tree

