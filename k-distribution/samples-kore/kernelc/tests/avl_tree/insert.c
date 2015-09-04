// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that inserts a new value into an avl tree. Note that many functions
 * below do not need specifications.
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

struct node* new_node(int v)
{
  struct node *node;
  node = (struct node *) malloc(sizeof(struct node));

  node->value = v;
  node->height = 1;
  node->left = NULL;
  node->right = NULL;

  return node;
}

struct node* insert(int v, struct node *t)
{
  if (t == NULL)
    return new_node(v);

  if (v < t->value)
    t->left = insert(v, t->left);
  else if (v > t->value)
    t->right = insert(v, t->right);
  else
    return t;

  update_height(t);
  t = balance(t);

  return t;
}

