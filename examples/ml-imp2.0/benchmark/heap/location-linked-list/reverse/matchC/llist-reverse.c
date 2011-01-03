#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* reverse(struct nodeList *x)
/*@ pre  < config > < env > x |-> ?x </ env > < heap > llist(?x)(A, LA) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env > < heap > llist(?x)(rev(A), rev(LA)) H </ heap >
                    < form > returns ?x </ form > C </ config > */
{
  struct nodeList *p;
  struct nodeList *y;
  p = 0 ;
  /*@ invariant < config > < env > p |-> ?p  x |-> ?x  y |-> ?y </ env >
                           < heap > llist(?p)(?B, ?LB) llist(?x)(?C, ?LC) H </ heap >
                           < form > (rev(A) === rev(?C) @ ?B) /\ (rev(LA) === rev(?LC) @ ?LB) </ form >
                           C </ config > */
  while(x != 0) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}


int main()
{
  struct nodeList *x;
  struct nodeList *y;
    
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 7;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 6;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 5;
  y->next = x;
  x = y;
  printf("x: %d %d %d\n",x, x->next, x->next->next);
  /*@ assert < config > < env > x |-> ?x  y |-> ?x </ env >
                        < heap > llist(?x)(!A, !LA) </ heap >
                        < form > TrueFormula </ form > </ config > */
  x = reverse(x) ;
  printf("x: %d %d %d\n",x, x->next, x->next->next);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > llist(?x)(rev(!A), rev(!LA)) </ heap >
                        < form > TrueFormula </ form > </ config > */
  return 0;
}


/*@ var ?x ?y ?p : ?Int */
/*@ var ?B ?C ?LB ?LC : ?Seq */
/*@ var !A !LA : !Seq */
/*@ var A LA : FreeSeq */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */
