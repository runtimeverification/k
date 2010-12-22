#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

struct nodeList* clpop(struct nodeList* x)
/*@ pre  < config > < env > x |-> x0 </ env >
                    < heap > x0 |-> v0 : (nodeList . val)
                            (x0 +Int 1) |-> ?t : (nodeList . next)
                             lseg(?t,x0)([?v] @ A)
                    H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env >  ?rho </ env >
                    < heap > x0 |-> v0 : (nodeList . val)
                            (x0 +Int 1) |-> ?aux : (nodeList . next)
                            lseg(?aux,x0)(A)
                    H </ heap > 
                    < form > returns x0 </ form > C </ config > */
{
  struct nodeList* t;
  struct nodeList* aux;
  t = x->next;
  if (x != t)
  {
    x->next = t->next;
    aux = t->next;
    free(t);
  }
  else
  {
    free(t);
  }
  return x;
}

/*@ verify */
int main()
{
  struct nodeList *x;
  struct nodeList *y;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 5;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 8;
  y->next = x;
  x->next = y;
  printf("%d %d\n", x->val, y->val);
  x = clpop(x);
  printf("%d\n", x->val);
  return 0;
}

/*@ var x0 v0 : FreeInt */
/*@ var ?x ?v ?t ?aux : ?Int */
/*@ var ?B ?C ?A1 ?A2 ?A ?A' : ?Seq */
/*@ var !A : !Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

