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


struct treeNode* insertRecursive(struct treeNode *t, int v)
/*@ pre  <config><env> t |-> ?root, v |-> v0 </env>
                 <heap> tree(?root)(T), H </heap>
                 C </config> /\ isBst(T) */
/*@ post <config><env> ?rho </env>
                 <heap> tree(?root)(?T), H </heap>
                 C </config> /\ isBst(?T)
                 /\ tree2mset(?T) = tree2mset(T) U {v0} /\ returns(?root) */
{
  if (t == 0)
    return newNode(v);

  if (v < t->val)
    t->left = insertRecursive(t->left, v);
  else
    t->right = insertRecursive(t->right, v);

  return t;
}

struct treeNode* insertIterative(struct treeNode *root, int v)
/*@ pre  <config><env> t |-> ?root, v |-> v0 </env>
                 <heap> tree(?root)(T), H </heap>
                 C </config> /\ isBst(T) */
/*@ post <config><env> ?rho </env>
                 <heap> tree(?root)(?T), H </heap>
                 C </config> /\ isBst(?T)
                 /\ tree2mset(?T) = tree2mset(T) U {v0} /\ returns(?root) */
{
  struct treeNode *t;
  struct treeNode *p;

  if (root == 0)
    return newNode(v);

  p = 0;
  t = root;
  /*@ invariant <config><env> root |-> ?root, t |-> ?root, p |-> 0 </env>
                        <heap> tree(?root)(T), H </heap> C </config>
                <config><env> root |-> ?root, t |-> ?t, p |-> ?p </env>
                        <heap> ?p |-> tree(?t)(?T), H </heap> C </config> */
  while (t != 0) {
    p = t;
    if (v < t->val)
      t = t->left;
    else
      t = t->right;
  }

  if (v < p->val)
    p->left = newNode(v);
  else
    p->right = newNode(v);

  return root;
}


struct treeNode* findRecursive(struct treeNode *t, int v)
/*@ pre  <config><env> t |-> root0, v |-> v0 </env>
                 <heap> tree(root0)(T), H </heap>
                 C </config> /\ isBst(T) */
/*@ post <config><env> ?rho </env>
                 <heap> tree(root0)(T), H </heap> 
                 C </ config > /\ isBst(T) /\ returns(?t)
                 /\ (~(?t = 0) /\ v0 in tree2mset(T)
                     \/ ?t = 0 /\ ~(v0 in tree2mset(T))) */
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
  return 0;
}


/*@ var ?n ?root ?t : ?Int */
/*@ var v0 root0 : FreeInt */
/*@ var ?T : ?Tree */
/*@ var T : FreeTree */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

