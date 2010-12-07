#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

/*@ verify */
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
  printf("x: %d %d %d\n",x->val, x->next->val, x->next->next->val);
  /*@ assert < config > < env > x |-> ?x  y |-> ?x </ env >
                        < heap > llist(?x)(!A, !LA) </ heap >
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
