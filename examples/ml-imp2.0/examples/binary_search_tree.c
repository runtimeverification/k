#include <stdlib.h>

struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};

struct treeNode* newNode(int v)
/*@ pre  < config > < env > v |-> v0 </ env > < heap > H </ heap > 
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap >
                      ?n |-> v0 : treeNode . val
                      ?n +Int 1 |-> 0 : treeNode . left
                      ?n +Int 2 |-> 0 : treeNode . right
                      H
                    </ heap >
                    < form > returns ?n </ form > C </ config > */
{
  struct treeNode *node;
  node = (struct treeNode *)malloc(sizeof(struct treeNode));
  node->val = v;
  node->left=node->right = 0;
  return node;
}

struct treeNode* insert(struct treeNode *t, int v)
/*@ pre  < config > < env > t |-> ?root  v |-> v0 </ env >
                    < heap > tree(?root)(T) H </ heap > 
                    < form > isBst(T) </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > tree(?root)(?T) H </ heap > 
                    < form >
                      isBst(?T) /\ tree2mset(?T) === tree2mset(T) U {| v0 |}
                      /\ returns ?root
                    </ form > C </ config > */
{
  if (t == 0)
    return newNode(v);
  if (v < t->val) t->left = insert(t->left, v);
    else t->right = insert(t->right, v);
  return t;
}


/*@ var ?n ?root : ?Int */
/*@ var v0 : FreeInt */
/*@ var ?T : ?Tree */
/*@ var T : FreeTree */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

