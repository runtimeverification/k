/*
 * Function that prints the contents of a binary tree in preorder traversal.
 */


#include <stdio.h>
#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


void preorder(struct treeNode *t)
/*@ rule <k> $ => return; ...</k> <heap>... tree(t)(T) ...</heap>
         <out>... . => tree2preorder(T) </out> */
{
  if (t == NULL)
    return;

  printf("%d ", t->val);
  preorder(t->left);
  preorder(t->right);
}


//@ var T : Tree

