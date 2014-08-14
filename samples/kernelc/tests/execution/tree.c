// Copyright (c) 2014 K Team. All Rights Reserved.
#include <stdlib.h>
#include <stdio.h>


struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};

struct listNode {
  int value;
  struct listNode *next;
};

struct stackNode {
  struct treeNode *value;
  struct stackNode *next;
};


struct listNode* tree_to_list_recursive(struct treeNode *t, struct listNode *l)
{
  struct listNode *ln;

  if (t == NULL)
    return l;

  ln = (struct listNode *) malloc(sizeof(struct listNode));
  ln->value = t->value;
  ln->next = tree_to_list_recursive(t->right, l);
  printf("%d ", t->value);
  l = tree_to_list_recursive(t->left, ln);
  free(t);

  return l;
}

struct listNode* tree_to_list_iterative(struct treeNode *t)
{
  struct listNode *l;
  struct stackNode *s;

  if (t == NULL)
    return NULL;

  l = NULL;
  s = (struct stackNode *) malloc(sizeof(struct stackNode));
  s->value = t;
  s->next = NULL;
  while (s != NULL) {
    struct treeNode *tn;
    struct listNode *ln;
    struct stackNode *sn;

    sn = s;
    s = s->next ;
    tn = sn->value;
    free(sn) ;
    if (tn->left != NULL) {
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->value = tn->left;
      sn->next = s;
      s = sn;
    }
    if (tn->right != NULL) {
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->value = tn;
      sn->next = s;
      s = sn;
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->value = tn->right;
      sn->next = s;
      s = sn;
      tn->left = NULL;
      tn->right = NULL;
    }
    else {
      ln = (struct listNode *) malloc(sizeof(struct listNode));
      ln->value = tn->value;
      ln->next = l;
      l = ln;
      printf("%d ", ln->value);
      free(tn);
    }
  }

  return l;
}


struct treeNode* create()
{
  struct treeNode* root;

  root = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->value = 4;
  root->left = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->left->value = 2;
  root->left->left = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->left->left->value = 1;
  root->left->left->left = NULL;
  root->left->left->right = NULL;
  root->left->right = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->left->right->value = 3;
  root->left->right->left = NULL;
  root->left->right->right = NULL;
  root->right = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->right->value = 6;
  root->right->left = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->right->left->value = 5;
  root->right->left->left = NULL;
  root->right->left->right = NULL;
  root->right->right = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->right->right->value = 7;
  root->right->right->left = NULL;
  root->right->right->right = NULL;

  return root;
}

void destroy(struct listNode* x)
{
  struct listNode *y;

  while(x) {
    y = x->next;
    free(x);
    x = y;
  }
}


int main()
{
  struct treeNode* t;
  struct listNode* l;

  t = create();
  l = tree_to_list_recursive(t, NULL);
  destroy(l);

  t = create();
  l = tree_to_list_iterative(t);
  destroy(l);

  return 0;
}

