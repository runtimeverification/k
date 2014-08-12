/*
 * Function that prints the contents of a binary tree in inorder traversal.
 */


#include <stdio.h>
#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


void inorder(struct treeNode *t)
/*@ rule <k> $ => return; ...</k> <heap>... tree(t)(T) ...</heap>
         <out>... . => tree2list(T) </out> */
{
  if (t == NULL)
    return;

  inorder(t->left);
  printf("%d ", t->val);
  inorder(t->right);
}


//@ var T : Tree

