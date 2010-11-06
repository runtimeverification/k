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

struct treeNode* find(struct treeNode *t, int v)
/*@ pre  < config > < env > t |-> root0  v |-> v0 </ env >
                    < heap > tree(root0)(T) H </ heap > 
                    < form > isBst(T) </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > tree(root0)(T) H </ heap > 
                    < form >
                      isBst(T) /\ returns ?t /\
                      (~(?t === 0) /\ v0 in tree2mset(T) \/
                       ?t === 0 /\ ~(v0 in tree2mset(T)))
                    </ form > C </ config > */
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


/*@ var ?n ?root ?t : ?Int */
/*@ var v0 root0 : FreeInt */
/*@ var ?T : ?Tree */
/*@ var T : FreeTree */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

