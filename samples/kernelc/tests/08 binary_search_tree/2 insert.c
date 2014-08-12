/*
 * Function that inserts a new value into a binary search tree.
 */


#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


struct treeNode* new_node(int v)
{
  struct treeNode *node;
  node = (struct treeNode *) malloc(sizeof(struct treeNode));
  node->val = v;
  node->left = NULL;
  node->right = NULL;
  return node;
}


struct treeNode* insert(int v, struct treeNode *t)
/*@ rule <k> $ => return ?t; ...</k>
         <heap>... tree(t)(T) => tree(?t)(?T) ...</heap>
    if isBst(T) /\ isBst(?T) /\ tree2mset(?T) = tree2mset(T) U {v} */
{
  if (t == NULL)
    return new_node(v);

  if (v < t->val)
    t->left = insert(v, t->left);
  else
    t->right = insert(v, t->right);

  return t;
}


//@ var T : Tree
