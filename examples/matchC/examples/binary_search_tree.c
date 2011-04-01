#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


struct treeNode *newNode(int v)
{
  struct treeNode *node;
  node = (struct treeNode *)malloc(sizeof(struct treeNode));
  node->val = v;
  node->left = node->right = 0;
  return node;
}


struct treeNode *insertRecursive(struct treeNode *t, int v)
/*@ cfg <heap_> tree(t)(T) => tree(?t)(?T) <_/heap>
    req isBst(T) /\ v0 = v
    ens isBst(?T) /\ tree2mset(?T) = tree2mset(T) U {v0} /\ returns(?t) */
{
  if (t == 0)
    return newNode(v);

  if (v < t->val)
    t->left = insertRecursive(t->left, v);
  else
    t->right = insertRecursive(t->right, v);

  return t;
}


struct treeNode *insertIterative(struct treeNode *root, int v)
{
  struct treeNode *t;
  struct treeNode *p;

  if (root == 0)
    return newNode(v);

  p = 0;
  t = root;
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


struct treeNode *findRecursive(struct treeNode *t, int v)
/*@ cfg <heap_> tree(t0)(T) <_/heap>
    req isBst(T) /\ t0 = t /\ v0 = v
    ens isBst(T) /\ returns(?r)
     /\ (~(?r = 0) /\ in(v0, tree2mset(T))
        \/ ?r = 0 /\ ~(in(v0, tree2mset(T)))) */
{
  if (t == 0)
    return 0;
  else if (v == t->val)
    return 1;
  else if (v < t->val)
    return findRecursive(t->left, v);
  else
    return findRecursive(t->right, v);
}


struct treeNode *deleteRecursive(struct treeNode *t, int v)
{
  if (t == 0)
    return 0;
  else if (v == t->val)
  {
    if (t->left && t->right)
    {
      t->val = min(t->right);
      t->right = deleteRecursive(t->right, t->val);
      return t;
    }
    else if (t->left)
      return t->left;
    else
      return t->right;
  }
  else if (v < t->val)
    return deleteRecursive(t->left, v);
  else
    return deleteRecursive(t->right, v);
}

int min(struct treeNode *t)
/*@ cfg <heap_> tree(t0)(T) <_/heap>
    req isBst(T) /\ t0 = t /\ ~(t = 0) 
    ens isBst(T) /\ returns(min(tree2mset(T))) */
{
  if (t->left)
    return (t->left);
  else
    return t->val;
}

int main()
{
  return 0;
}


//@ var r : Int
//@ var T : Tree

