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
          < heap > queue(x0)(A) H </ heap >
          < form > TrueFormula </ form > C </ config > */
/*@ post  < config > 
          < env > ?rho </ env > 
          < heap > queue(x0)(A @ [val0]) H </ heap >
          < form > returns x0 </ form > C </ config > */
{
  struct nodeList* n;
  n = (struct nodeList*)malloc(sizeof(struct nodeList));
  n->val = val;
  n->next = x;
  
  if (x != 0)
  {
    if (x->head != 0)
    {
      x->tail->next = n ;
    }
    else 
    {
      x->head = n ;
    }
    x->tail = n;
  }
  return x;
}

int main()
{
  struct nodeQueue *x;
  struct nodeList *hd;
  struct nodeList *tl;
  x = (struct nodeQueue*)malloc(sizeof(struct nodeQueue));
  hd = (struct nodeList*)malloc(sizeof(struct nodeList));
  tl = (struct nodeList*)malloc(sizeof(struct nodeList));
  
  return 0;
}

/*@ var x0 val0 : FreeInt */
/*@ var A : FreeSeq */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

