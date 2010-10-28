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

struct treeNodeList {
  struct treeNode *val;
  struct treeNodeList *next;
};


struct nodeList *toListIterative(struct treeNode *root)
/*@ pre  < config > < env > root |-> ?root </ env >
                    < heap > tree(?root)(T) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > list(?a)(tree2seq(T)) H </ heap >
                    < form > returns ?a </ form > C </ config > */
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
  /*@ invariant
        < config >
          < env >
            root |-> ?root  a |-> ?a  stack |-> ?stack
            t |-> ?t  x |-> ?x  node |-> ?node
          </ env >
          < heap > list{tree}(?stack)(?TS) list(?a)(?A) H </ heap >
          < form > tree2seq(T) === seq{tree}2seq(rev(?TS)) @ ?A </ form >
          C
        </ config > */
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
  /*@ assert < config >
             < env >
               root |-> ?root  tl |-> ?tl  tr |-> ?tr  test |-> ?test
             </ env >
             < heap > tree(?root)(!T) </ heap >
             < form > TrueFormula </ form > </ config > */
  test = toListIterative(root);
  /*@ assert < config >
             < env >
               root |-> ?root  tl |-> ?tl  tr |-> ?tr  test |-> ?test
             </ env >
             < heap > list(?test)(tree2seq(!T)) </ heap >
             < form > TrueFormula </ form > </ config > */
  return 0;
}


/*@ var ?root ?a ?stack ?t ?x ?node ?tl ?tr ?test : ?Int */
/*@ var ?TS ?A : ?Seq */
/*@ var T : FreeTree */
/*@ var !T : !Tree */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

