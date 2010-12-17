#include <stdlib.h>
#include <stdio.h>

struct nodeList {
int val;
struct nodeList *next;
};

struct nodeQueue {
struct nodeList* head;
struct nodeList* tail;
};


struct nodeQueue* enqueue(struct nodeQueue *x, int val)
/*@ pre   < config > 
          < env > x |-> x0 val |-> val0 </ env > 
          < heap > 
              x0 |-> ?hd : (nodeQueue . head)
              (x0 +Int 1) |-> ?tl : (nodeQueue . tail )
              queue(?hd, ?tl)(A)  
              H 
          </ heap >
          < form > ~(x0 === 0) /\ ~(?hd === 0) /\ ~(?tl === 0) /\ ~(A === epsilon) </ form > C </ config > */
/*@ post  < config > 
          < env > ?rho </ env > 
          < heap > queue(x0)([val0] @ A) H </ heap >
          < form > returns x0 </ form > C </ config > */
{
  struct nodeList* n;
  n = (struct nodeList*)malloc(sizeof(struct nodeList));
  n->val = val;
  n->next = x->head;
  x->head = n;
  
/*@ assert < config > 
          < env > x |-> x0 val |-> val0 n |-> ?n </ env > 
          < heap > 
              ?n |-> val0 : (nodeList . val)
              (?n +Int 1) |-> ?hd : (nodeList . next)
              x0 |-> ?n : (nodeQueue . head)
              (x0 +Int 1) |-> ?tl : (nodeQueue . tail )
              queue(?hd,?tl)(A)  
              H 
          </ heap >
          < form > ~(x0 === 0) /\ ~(?hd === 0) /\ ~(?tl === 0) /\ ~(A === epsilon) </ form > C </ config > */
/*@ assert < config > 
          < env > x |-> x0 val |-> val0 n |-> ?n </ env > 
          < heap > 
              lseg(?n,?hd)([val0])
              x0 |-> ?n : (nodeQueue . head)
              (x0 +Int 1) |-> ?tl : (nodeQueue . tail )
              queue(?hd,?tl)(A)  
              H 
          </ heap >
          < form > ~(x0 === 0) /\ ~(?hd === 0) /\ ~(?tl === 0) /\ ~(A === epsilon) </ form > C </ config > */
/*@ assert < config > 
          < env > x |-> x0 val |-> val0 n |-> ?n </ env > 
          < heap > 
              x0 |-> ?n : (nodeQueue . head)
              (x0 +Int 1) |-> ?tl : (nodeQueue . tail )
              queue(?n,?tl)([val0] @ A)  
              H 
          </ heap >
          < form > ~(x0 === 0) /\ ~(?hd === 0) /\ ~(?tl === 0) /\ ~(A === epsilon) </ form > C </ config > */
  return x;
}

int main()
{
  struct nodeQueue* x;
  struct nodeList *f;
  struct nodeList* l;

  f = (struct nodeList*)malloc(sizeof(struct nodeList));
  l = (struct nodeList*)malloc(sizeof(struct nodeList));
  x = (struct nodeQueue*)malloc(sizeof(struct nodeQueue));
  l->val=6;
  l->next=0;
  f->val = 5;
  f->next = l;
  x->head=f;
  x->tail=l;
  printf("%d %d\n",x->head->val, x->tail->val);
  x = enqueue(x,10);
  printf("%d %d %d\n",x->head->val, x->head->next->val,x->tail->val);
  return 0;
}

/*@ var x0 val0 : FreeInt */
/*@ var ?n ?x ?u ?v ?hd ?tl : ?Int */
/*@ var A : FreeSeq */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var !H : !MapItem */
/*@ var C : FreeBagItem */

