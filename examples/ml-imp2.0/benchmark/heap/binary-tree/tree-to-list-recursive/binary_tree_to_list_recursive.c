#include <stdlib.h>

struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


struct nodeList {
  int val;
  struct nodeList *next;
};
  
struct nodeList *toListRecursive(struct treeNode *root, struct nodeList *x)
{
  struct nodeList *node;
  if (root == 0)
    return x;
  node = (struct nodeList *) malloc(sizeof(struct nodeList));
  node->val = root->val; 
  node->next = toListRecursive(root->right, x);
  node = toListRecursive(root->left, node);
  free(root);
  return node;
}

