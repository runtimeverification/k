/*
 * Function that searches a binary search tree for a node with a certain value.
 */


#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


int find(int v, struct treeNode *t)
/*@ rule <k> $ => return r; ...</k> <heap>... tree(t)(T) ...</heap>
    if isBst(T) /\ (~(r = 0) <==> in(v, tree2mset(T))) */
{
  if (t == NULL) return 0;
  if (v == t->val) return 1;
  if (v < t->val) return find(v, t->left);
  return find(v, t->right);
}


//@ var r : Int
//@ var T : Tree

