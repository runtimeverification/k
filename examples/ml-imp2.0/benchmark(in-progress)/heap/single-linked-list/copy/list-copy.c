#include <stdlib.h>


struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList *copy(struct nodeList *x)
/*@ pre  < config > < env > x |-> x0 </ env >
                    < heap > list(x0)(A) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > list(x0)(A) list(?y)(A) H </ heap >
                    < form > returns ?y </ form > C </ config > */
{
  struct nodeList* y;
  struct nodeList* iterx;
  struct nodeList* itery;
  struct nodeList* newnode;

  if (x == 0)
    return 0;

  y = (struct nodeList *)malloc(sizeof(struct nodeList));
  y->val = x->val;
  y->next = 0;
  iterx = x->next;
  itery = y;
  /*@ invariant < config > < env >
                             iterx |-> ?ix itery |-> ?iy newnode |-> ?n
                             x |-> x0 y |-> ?y 
                           </ env >
                           < heap >
                             lseg(x0,?ix)(?A @ [?v]) list(?ix)(?B)
                             lseg(?y,?iy)(?A)
                             ?iy |-> ?v : (nodeList . val)
                             ?iy +Int 1 |-> 0 : (nodeList . next)
                             H
                           </ heap >
                           < form > A === (?A @ [?v] @ ?B) </ form >
                           C </ config > */
  while(iterx) {
    newnode = (struct nodeList *)malloc(sizeof(struct nodeList));
    newnode->val = iterx->val;
    newnode->next = 0;
    itery->next = newnode;
    iterx = iterx->next;
    itery = newnode;
  }

  return y;
}

/*@ var ?y ?ix ?iy ?v ?n : ?Int */
/*@ var x0 : FreeInt */
/*@ var ?A ?B ?C : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */
