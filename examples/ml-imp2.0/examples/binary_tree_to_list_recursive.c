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
/*@ pre < config > < env > root |-> ?root x |-> ?x </ env >
                   < heap > tree(?root)(Tree) list(?x)(A) heapFrame </ heap >
                   < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > list(?x)(tree2seq(Tree) @ A) heapFrame </ heap >
                    < form > returns ?x </ form > </ config > */
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

/*@ var ?root ?x : ?Int */
/*@ var ?rho : ?MapItem */
/*@ var heapFrame : FreeMapItem */
/*@ var Tree : FreeTree */
/*@ var ?T : ?Tree */
/*@ var A : FreeSeq */

