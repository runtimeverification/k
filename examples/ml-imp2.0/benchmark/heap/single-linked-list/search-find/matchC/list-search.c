#include <stdlib.h>


struct nodeList {
  int val;
  struct nodeList *next;
};

int search(struct nodeList* x, int value)
/*@ pre  < config > < env > x |-> x0 value |-> val0 </ env >
                    < heap > list(x0)(A) H </ heap >
                    < form > ~(x0 === 0) /\ ~(A === epsilon) </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > list(x0)(A) H </ heap >
                    < form > returns ?f /\ (?f === found(A,val0)) </ form > C </ config > */
{
  struct nodeList* iterx;
  int f;
  f = 0;
  iterx = x;
  x->val = x->val;
/*@ invariant < config > 
              < env >
              iterx |-> ?ix x |-> x0 f |-> ?f value |-> val0 
              </ env >
              < heap >
              lseg(x0,?ix)(?A)
              list(?ix)(?A')
              H
              </ heap >
              < form > A === (?A @ ?A') /\ (?f === found(?A,val0)) </ form >
              C </ config > */
  while(iterx != 0)
  {
    if (iterx->val == value) f = 1;
    iterx = iterx->next;
  }
  return f;
}

int main()
{
  struct nodeList *x;
  struct nodeList *y;
  int l;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 5;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 7;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 45;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 5;
  y->next = x;
  x = y;
  l = search(x,5);
  return 0;
}

/*@ var ?ix ?v ?n ?f : ?Int */
/*@ var x0 val0 : FreeInt */
/*@ var ?A ?A' : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

