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
/*@ pre  < config > < env > t |-> ?t  l |-> ?l </ env >
                    < heap > tree(?t)(T) list(?l)(A) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > list(?l)(tree2list(T) @ A) H </ heap >
                    < form > returns ?l </ form > C </ config > */
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
/*@ pre  < config > < env > t |-> ?t </ env >
                    < heap > tree(?t)(T) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > list(?l)(tree2list(T)) H </ heap >
                    < form > returns ?l </ form > C </ config > */
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
  /*@ invariant
        < config >
          < env >
            t |-> ?t  l |-> ?l  s |-> ?s
            tn |-> ?tn  ln |-> ?ln  sn |-> ?sn
          </ env >
          < heap > list{tree}(?s)(?TS) list(?l)(?A) H </ heap >
          < form > tree2list(T) === list{tree}2list(rev(?TS)) @ ?A </ form >
          C
        </ config > */
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
  /*@ assert < config > < env > t |-> ?t  l |-> ?l </ env >
                        < heap > tree(?t)(!T1) </ heap >
                        < form > TrueFormula </ form > </ config > */
  l = toListRecursive(t, 0);
  /*@ assert < config > < env > t |-> ?t  l |-> ?l </ env >
                        < heap > list(?l)(tree2list(!T1)) </ heap >
                        < form > TrueFormula </ form > </ config > */
  printf("l: ");
  print(l);
  destroy(l);
  /*@ assert < config > < env > t |-> ?t  l |-> ?l </ env >
                        < heap > (.).Map </ heap >
                        < form > TrueFormula </ form > </ config > */


  t = create();
  /*@ assert < config > < env > t |-> ?t  l |-> ?l </ env >
                        < heap > tree(?t)(!T2) </ heap >
                        < form > TrueFormula </ form > </ config > */
  l = toListIterative(t);
  /*@ assert < config > < env > t |-> ?t  l |-> ?l </ env >
                        < heap > list(?l)(tree2list(!T2)) </ heap >
                        < form > TrueFormula </ form > </ config > */
  printf("l: ");
  print(l);
  destroy(l);
  /*@ assert < config > < env > t |-> ?t  l |-> ?l </ env >
                        < heap > (.).Map </ heap >
                        < form > TrueFormula </ form > </ config > */

  return 0;
}


/*@ var ?t ?tn ?s ?sn ?l ?ln : ?Int */
/*@ var ?TS ?A : ?Seq */
/*@ var A : FreeSeq */
/*@ var !T1 !T2 : !Tree */
/*@ var T : FreeTree */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

