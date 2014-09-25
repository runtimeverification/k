// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that deletes the node of the tree having a certain value and
 * rebalances the tree to be an avl tree. Note that many functions below do not
 * need specifications.
 */

#include<stdlib.h>

struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};

int max(int a, int b)
{
  return a > b ? a : b;
}

int height(struct node *t)
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
{
  if (t->left == NULL)
    return t->value;
  else
    return find_min(t->left);
}

struct node* delete(int v, struct node *t)
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

