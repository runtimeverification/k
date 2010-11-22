#include <stdlib.h>
#include <stdio.h>

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


struct nodeList *toListRecursive(struct treeNode *root, struct nodeList *x)
/*@ pre  < config > < env > root |-> ?root  x |-> ?x </ env >
                    < heap > tree(?root)(T) list(?x)(A) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > list(?x)(tree2seq(T) @ A) H </ heap >
                    < form > returns ?x </ form > C </ config > */
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


void destroy(struct nodeList* x)
{
  struct nodeList *y;
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct nodeList* x)
{
  while(x)
  {
    printf("%d ",x->val);
    x = x->next;
  }
  printf("\n"); 
}


/*@ verify */
int main()
{
  struct treeNode* root;
  struct nodeList* node;

  root = sample();
  /*@ assert < config > < env > root |-> ?root  node |-> ?node </ env >
                        < heap > tree(?root)(!T1) </ heap >
                        < form > TrueFormula </ form > </ config > */
  node = toListRecursive(root, 0);
  /*@ assert < config > < env > root |-> ?root  node |-> ?node </ env >
                        < heap > list(?node)(tree2seq(!T1)) </ heap >
                        < form > TrueFormula </ form > </ config > */
  printf("list: ");
  print(node);
  destroy(node);
  /*@ assert < config > < env > root |-> ?root  node |-> ?node </ env >
                        < heap > (.).Map </ heap >
                        < form > TrueFormula </ form > </ config > */


//  root = sample();
//  /*@ assert < config > < env > root |-> ?root  node |-> ?node </ env >
//                        ***(< heap > tree(?root)(((upsilon[1]upsilon)[2](upsilon[3]upsilon))[4]((upsilon[5]upsilon)[6](upsilon[7]upsilon))) </ heap > ***)
//                        < heap > tree(?root)((upsilon[1]upsilon)[2](upsilon[3]upsilon)) </ heap >
//                        < form > TrueFormula </ form > </ config > */
//  node = toListIterative(root);
//  /*@ assert < config > < env > root |-> ?root  node |-> ?node </ env >
//                        < heap > list(?node)([1, 2, 3, 4, 5, 6, 7]) </ heap >
//                        < form > TrueFormula </ form > </ config > */
//  destroy(node);
//  /*@ assert < config > < env > root |-> ?root  node |-> ?node </ env >
//                        < heap > (.).Map </ heap >
//                        < form > TrueFormula </ form > </ config > */
  root = sample();
  /*@ assert < config > < env > root |-> ?root  node |-> ?node </ env >
                        < heap > tree(?root)(!T2) </ heap >
                        < form > TrueFormula </ form > </ config > */
  node = toListIterative(root);
  /*@ assert < config > < env > root |-> ?root  node |-> ?node </ env >
                        < heap > list(?node)(tree2seq(!T2)) </ heap >
                        < form > TrueFormula </ form > </ config > */
  printf("list: ");
  print(node);
  destroy(node);
  /*@ assert < config > < env > root |-> ?root  node |-> ?node </ env >
                        < heap > (.).Map </ heap >
                        < form > TrueFormula </ form > </ config > */

  return 0;
}


/*@ var ?root ?a ?stack ?t ?x ?node ?tl ?tr ?test : ?Int */
/*@ var ?TS ?A : ?Seq */
/*@ var A : FreeSeq */
/*@ var T : FreeTree */
/*@ var !T1 !T2 : !Tree */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

