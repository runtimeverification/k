#include <stdlib.h>

struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


struct treeNode* newNode(int v)
{
  struct treeNode *node;
  node = (struct treeNode *)malloc(sizeof(struct treeNode));
  node->val = v;
  node->left=node->right = 0;
  return node;
}


struct treeNode* insert(struct treeNode *t, int v)
{
  if (t == 0)
    return newNode(v);
  if (v < t->val) t->left = insert(t->left, v);
    else t->right = insert(t->right, v);
  return t;
}


struct treeNode* find(struct treeNode *t, int v)
{
  if (t == 0)
    return 0;
  else if (v == t->val)
    return t;
  else if (v < t->val)
    return find(t->left, v);
  else
    return find(t->right, v);
}

int main()
{
  struct treeNode* tn;
  tn = (struct treeNode*)malloc(sizeof(treeNode));
  tn->val = 7;
  tn->left = 0;
  tn->right = 0;
  tn = insert(tn, 30);
  tn = insert(tn, 3);
  tn = insert(tn, 5);
  tn = insert(tn, 6);
  tn = insert(tn, 12);
  tn = insert(tn, 9);
  
  return 0;
}

