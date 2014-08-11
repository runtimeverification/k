/*
 * Function that deletes the node of the tree having a certain value and 
 * rebalances the tree to be an avl tree.  The same comments as in the delete
 * of binary search trees and as in the insert of avl trees apply.
 *
 * WARNING: this example takes about 2 minutes to verify.
 */


#include<stdlib.h>


struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};


int max(int a, int b)
//@ rule <k> $ => return maxInt(a, b); ...</k>
{
  return a > b ? a : b;
}


int height(struct node *t)
/*@ rule <k> $ => return height(T); ...</k> <heap>... htree(t)(T) ...</heap>
    if isHeightTree(heights(T)) */
{
  return t ? t->height : 0;
}


void update_height(struct node *t)
{
  t->height = max(height(t->left), height(t->right)) + 1;
}


struct node* left_rotate(struct node *x)
{
  struct node *y;

  y = x->right;
  x->right = y->left;
  y->left = x;

  update_height(x); 
  update_height(y); 

  return y;
}


struct node* right_rotate(struct node *x)
{
  struct node *y;

  y = x->left;
  x->left = y->right;
  y->right = x;

  update_height(x); 
  update_height(y); 

  return y;
}


struct node* balance(struct node *t)
{
  if (height(t->left) - height(t->right) > 1) {
    if (height(t->left->left) < height(t->left->right))
      t->left = left_rotate(t->left);
    t = right_rotate(t);
  }
  else if (height(t->left) - height(t->right) < -1) {
    if (height(t->right->left) > height(t->right->right))
      t->right = right_rotate(t->right);
    t = left_rotate(t);
  }

  return t;
}


int find_min(struct node *t)
/*@ rule <k> $ => return m; ...</k> <heap>... htree(t)(T) ...</heap>
    if ~(t = 0) /\ isBst(values(T))
       /\ in(m, tree2mset(values(T))) /\ leq({m}, tree2mset(values(T))) */
{
  if (t->left == NULL) return t->value;
  return find_min(t->left);
}


struct node* delete(int v, struct node *t)
/*@ rule <k> $ => return ?t; ...</k>
         <heap>... htree(t)(T) => htree(?t)(?T) ...</heap>
    if isAvl(T) /\ isAvl(?T)
       /\ tree2mset(values(?T)) = diff(tree2mset(values(T)), {v})
       /\ 0 <= height(T) - height(?T) /\ height(T) - height(?T) <= 1 */
{
  int min;

  if (t == NULL)
    return NULL;

  if (v == t->value) {
    if (t->left == NULL) {
      struct node *temp;

      temp = t->right;
      free(t);

      return temp;
    }
    else if (t->right == NULL) {
      struct node *temp;

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

  update_height(t);
  t = balance(t);

  return t;
}


//@ var m : Int
//@ var T : Tree
