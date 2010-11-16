#include <stdlib.h>
#include <stdio.h>

struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};

struct listNode {
  int val;
  struct listNode *next;
};

struct stackNode {
  struct treeNode *val;
  struct stackNode *next;
};


struct listNode *toListRecursive(struct treeNode *tree, struct listNode *list)
{
  struct listNode *ln;

  if (tree == 0)
    return list;

  ln = (struct listNode *) malloc(sizeof(struct listNode));
  ln->val = tree->val; 
  ln->next = toListRecursive(tree->right, list);
  list = toListRecursive(tree->left, ln);
  free(tree);

  return list;
}


struct listNode *toListIterative(struct treeNode *tree)
{
  struct listNode *list;
  struct listNode *ln;
  struct treeNode *tn;
  struct stackNode *stack;
  struct stackNode *sn;

  if (tree == 0)
    return 0;

  list = 0;
  stack = (struct stackNode *) malloc(sizeof(struct stackNode));
  stack->val = tree;
  stack->next = 0;
  while (stack != 0) {
    sn = stack;
    stack = stack->next ;
    tn = sn->val;
    free(sn) ;
    if (tn->left != 0) {
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn->left;
      sn->next = stack;
      stack = sn;
    }
    if (tn->right != 0) {
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn;
      sn->next = stack;
      stack = sn;
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn->right;
      sn->next = stack;
      stack = sn;
      tn->left = tn->right = 0;
    }
    else {
      ln = (struct listNode *) malloc(sizeof(struct listNode));
      ln->val = tn->val;
      ln->next = list;
      list = ln;
      free(tn);
    }
  }

  return list;
}


struct treeNode *sample()
{
  struct treeNode* root;

  root = (struct treeNode*)malloc(sizeof(struct treeNode));
  root->val = 4;
  root->left = (struct treeNode*)malloc(sizeof(struct treeNode));
  root->left->val = 2;
  root->left->left = (struct treeNode*)malloc(sizeof(struct treeNode));
  root->left->left->val = 1;
  root->left->left->left = 0;
  root->left->left->right = 0;
  root->left->right = (struct treeNode*)malloc(sizeof(struct treeNode));
  root->left->right->val = 3;
  root->left->right->left = 0;
  root->left->right->right = 0;
  root->right = (struct treeNode*)malloc(sizeof(struct treeNode));
  root->right->val = 6;
  root->right->left = (struct treeNode*)malloc(sizeof(struct treeNode));
  root->right->left->val = 5;
  root->right->left->left = 0;
  root->right->left->right = 0;
  root->right->right = (struct treeNode*)malloc(sizeof(struct treeNode));
  root->right->right->val = 7;
  root->right->right->left = 0;
  root->right->right->right = 0;

  return root;
}


void destroy(struct listNode* x)
{
  struct listNode *y;
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct listNode* x)
{
  while(x)
  {
    printf("%d ",x->val);
    x = x->next;
  }
  printf("\n"); 
}


int main()
{
  struct treeNode* tree;
  struct listNode* list;

  tree = sample();
  list = toListRecursive(tree, 0);
  printf("list: ");
  print(list);
  destroy(list);

  tree = sample();
  list = toListIterative(tree);
  printf("list: ");
  print(list);
  destroy(list);

  return 0;
}

