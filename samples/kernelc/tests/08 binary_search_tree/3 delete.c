/*
 * Function that deletes the node of the tree having a certain value and 
 * rebalances the tree to be a binary search tree.  Auxilliary function
 * find_min returns the leftmost leaf of a tree (holding its smallest element).
 */


#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


int find_min(struct treeNode *t)
/*@ rule <k> $ => return m; ...</k> <heap>... tree(t)(T) ...</heap>
    if ~(t = 0) /\ isBst(T) /\ in(m, tree2mset(T)) /\ leq({m}, tree2mset(T)) */
{
  if (t->left == NULL) return t->val;
  return find_min(t->left);
}


struct treeNode* delete(int v, struct treeNode *t)
/*@ rule <k> $ => return ?t; ...</k>
         <heap>... tree(t)(T) => tree(?t)(?T) ...</heap>
    if isBst(T) /\ isBst(?T) /\ tree2mset(?T) = diff(tree2mset(T), {v}) */
{
  int min;

  if (t == NULL)
    return NULL;

  if (v == t->val) {
    if (t->left == NULL) {
      struct treeNode *tmp;

      tmp = t->right;
      free(t);

      return tmp;
    }
    else if (t->right == NULL) {
      struct treeNode *tmp;

      tmp = t->left;
      free(t);

      return tmp;
    }
    else {
      min = find_min(t->right);
      t->right = delete(min, t->right);
      t->val = min;
    }
  }
  else if (v < t->val)
    t->left = delete(v, t->left);
  else
    t->right = delete(v, t->right);

  return t;
}


//@ var m : Int
//@ var T : Tree

