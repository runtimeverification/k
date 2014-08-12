/*
 * Function that searches an avl tree for a node with a certain value.  It is
 * almost identical to the find function of binary search trees.  The fact that
 * the tree is an avl does not matter in this case.  The structural difference
 * between an avl tree and a binary search tree as mathematical objects is that
 * an avl tree holds pairs (value,height) in its nodes.  In the function
 * specification below, values(T) is the binary search tree holding only the
 * value component of each node (and dropping the height component).
 */


#include<stdlib.h>


struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};


int find(int v, struct node *t)
/*@ rule <k> $ => return r; ...</k> <heap>... htree(t)(T) ...</heap>
    if isBst(values(T)) /\ (~(r = 0) <==> in(v, tree2mset(values(T)))) */
{
  if (t == NULL) return 0;
  if (v == t->value) return 1;
  if (v < t->value) return find(v, t->left);
  return find(v, t->right);
}


//@ var r : Int
//@ var T : Tree

