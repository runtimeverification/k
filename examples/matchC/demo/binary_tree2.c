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


struct listNode *toListRecursive(struct treeNode *t, struct listNode *l)
{
  struct listNode *ln;

  if (t == 0)
    return l;

  ln = (struct listNode *) malloc(sizeof(struct listNode));
  ln->val = t->val; 
  ln->next = toListRecursive(t->right, l);
  l = toListRecursive(t->left, ln);
  free(t);

  return l;
}


struct listNode *toListIterative(struct treeNode *t)
{
  struct listNode *l;
  struct listNode *ln;
  struct treeNode *tn;
  struct stackNode *s;
  struct stackNode *sn;

  if (t == 0)
    return 0;

  l = 0;
  s = (struct stackNode *) malloc(sizeof(struct stackNode));
  s->val = t;
  s->next = 0;
  while (s != 0) {
    sn = s;
    s = s->next ;
    tn = sn->val;
    free(sn) ;
    if (tn->left != 0) {
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn->left;
      sn->next = s;
      s = sn;
    }
    if (tn->right != 0) {
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn;
      sn->next = s;
      s = sn;
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn->right;
      sn->next = s;
      s = sn;
      tn->left = tn->right = 0;
    }
    else {
      ln = (struct listNode *) malloc(sizeof(struct listNode));
      ln->val = tn->val;
      ln->next = l;
      l = ln;
      free(tn);
    }
  }

  return l;
}


struct treeNode *create()
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
  struct treeNode* t;
  struct listNode* l;

  t = create();
  //@ assert <heap> tree(t)(!T1) </heap>
  l = toListRecursive(t, 0);
  //@ assert <heap> list(l)(tree2list(!T1)) </heap>
  printf("l: ");
  print(l);
  destroy(l);
  //@ assert <heap> . </heap>

  t = create();
  //@ assert <heap> tree(t)(!T2) </heap>
  l = toListIterative(t);
  //@ assert <heap> list(l)(tree2list(!T2)) </heap>
  printf("l: ");
  print(l);
  destroy(l);
  //@ assert <heap> . </heap>

  return 0;
}


//@ var T : Tree

