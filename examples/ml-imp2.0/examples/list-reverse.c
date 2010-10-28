#include <stdlib.h>


struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* reverse(struct nodeList *x)
/*@ pre  < config > < env > x |-> ?x </ env > < heap > list(?x)(A) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(?x)(rev(A)) H </ heap >
                    < form > returns ?x </ form > C </ config > */
{
  struct nodeList *p;
  struct nodeList *y;
  p = 0 ;
  /*@ invariant < config > < env > p |-> ?p x |-> ?x y |-> ?y </ env >
                           < heap > list(?p)(?B) list(?x)(?C) H </ heap >
                           < form > rev(A) === rev(?C) @ ?B </ form >
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
  /*@ assert < config > 
             < env > x |-> ?x y |-> ?x </ env > 
             < heap > list(?x)([5] @ [6] @ [7]) </ heap > 
             < form > TrueFormula </ form > </ config > */
  x = reverse(x) ;
  /*@ assert < config > < env > x |-> ?x y |-> ?y </ env > < heap > list(?x)([7] @ [6] @ [5]) </ heap > < form > TrueFormula </ form > </ config > */
  y = x;
  x = x->next;
  free(y);
  y = x;
  x = x->next;
  free(y);
  y = x;
  x = x->next;
  free(y);
  /*@ assert < config > < env > x |-> ?x y |-> ?y </ env > < heap > list(0)(epsilon) </ heap > < form > TrueFormula </ form > </ config > */
  
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
  /*@ assert < config > < env > x |-> ?x y |-> ?x </ env > < heap > list(?x)(!A) </ heap > < form > TrueFormula </ form > </ config > */
  x = reverse(x) ;
  /*@ assert < config > < env > x |-> ?x y |-> ?y </ env > < heap > list(?x)(rev(!A)) </ heap > < form > TrueFormula </ form > </ config > */
  return 0;
}


/*@ var ?x ?y ?p : ?Int */
/*@ var ?B ?C : ?Seq */
/*@ var !A : !Seq */
/*@ var A : FreeSeq */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */
