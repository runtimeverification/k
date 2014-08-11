/*
 * Function that prints the contents of a binary tree in postorder traversal.
 */


#include <stdio.h>
#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


void postorder(struct treeNode *t)
/*@ rule <k> $ => return; ...</k> <heap>... tree(t)(T) ...</heap>
         <out>... . => tree2postorder(T) </out> */
{
  if (t == NULL)
    return;

  postorder(t->left);
  postorder(t->right);
  printf("%d ", t->val);
}


//@ var T : Tree

