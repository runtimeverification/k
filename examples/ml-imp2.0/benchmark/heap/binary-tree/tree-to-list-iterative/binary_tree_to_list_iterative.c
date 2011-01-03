#include <stdlib.h>
#include <stdio.h>

struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};

struct nodeList {
  int val;
  struct nodeList *next;
};

struct treeNodeList {
  struct treeNode *val;
  struct treeNodeList *next;
};


struct nodeList *toListIterative(struct treeNode *root)
{
  struct nodeList *a;
  struct nodeList *node;
  struct treeNode *t;
  struct treeNodeList *stack;
  struct treeNodeList *x;

  if (root == 0)
    return 0;
  a = 0;
  stack = (struct treeNodeList *) malloc(sizeof(struct treeNodeList));
  stack->val = root;
  stack->next = 0;
  while (stack != 0) {
    x = stack;
    stack = stack->next ;
    t = x->val;
    free(x) ;
    if (t->left != 0) {
      x = (struct treeNodeList *) malloc(sizeof(struct treeNodeList));
      x->val = t->left;
      x->next = stack;
      stack = x;
    }
    if (t->right != 0) {
      x = (struct treeNodeList *) malloc(sizeof(struct treeNodeList));
      x->val = t;
      x->next = stack;
      stack = x;
      x = (struct treeNodeList *) malloc(sizeof(struct treeNodeList));
      x->val = t->right;
      x->next = stack;
      stack = x;
      t->left = t->right = 0;
    }
    else {
      node = (struct nodeList *) malloc(sizeof(struct nodeList));
      node->val = t->val;
      node->next = a;
      a = node;
      free(t);
    }
  }
  return a;
}

int main()
{
  struct treeNode* root;
  struct treeNode* tl;
  struct treeNode* tr;
  struct nodeList *test;
  root = (struct treeNode*)malloc(sizeof(struct treeNode));
  tl = (struct treeNode*)malloc(sizeof(struct treeNode));
  tr = (struct treeNode*)malloc(sizeof(struct treeNode));
  root->val = 8;
  tl->val = 4;
  tr->val = 12;
  root->left = tl;
  root->right = tr;
  tl->left = 0;
  tl->right = 0;
  tr->left = 0;
  tr->right = 0;
  printf("Left root right:\n  %d   %d   %d\n", tl->val, root->val, tr->val);
  test = toListIterative(root);
  return 0;
}

