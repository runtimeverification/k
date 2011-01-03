
#include "tree.h"

/*@ requires valid_tree(t)
  @ ensures \result != \null => (path(t,\result) && \result->node == v) */
tree brute_force_search(tree t, int v) {
  tree u;
  if (t == NULL) return NULL;
  if (t->node == v) return t;
  u = brute_force_search(t->left, v);
  if (u != NULL) return u;
  return brute_force_search(t->right, v);
}

/*@ requires valid_tree(t) && bst(t)
  @ ensures \result != \null => (path(t,\result) && \result->node == v) */
tree binary_search(tree t, int v) {
  if (t == NULL) return NULL;
  if (t->node == v) return t;
  if (v < t->node) 
    return binary_search(t->left,  v);
  else
    return binary_search(t->right, v);
}

/*@ requires 
  @   valid_tree(t)
  @ ensures 
  @   \result => (bst(t) && \forall int x; in_tree(x, t) => min <= x <= max)
  @*/
int is_bst(tree t, int min, int max) {
  if (t == NULL) return 1;
  if (t->node < min || t->node > max) return 0;
  return (is_bst(t->left, min, t->node) && is_bst(t->right, t->node, max));
}

/*@ requires valid_tree(t)
  @ ensures \result <=> heap(t)
  @*/
int is_heap(tree t) {
  if (t == NULL) return 1;
  if (t->left != NULL && t->left->node >= t->node) return 0;
  if (t->right != NULL && t->right->node >= t->node) return 0;
  return is_heap(t->left) && is_heap(t->right);
}
