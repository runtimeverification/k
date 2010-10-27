#include <stdlib.h>


struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* reverse(struct nodeList *x)
/*@ pre < config > < env > x |-> ?x ?env </ env > < heap > list(?x)(A) heapFrame </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(?x)(rev(A)) heapFrame </ heap > < form > returns ?x </ form > </ config > */
{
  struct nodeList *p;
  struct nodeList *y;
  p = 0 ;
  /*@ invariant < config > < env > p |-> ?p x |-> ?x y |-> ?y ?env  </ env >
                          < heap > list(?p)(?B) list(?x)(?C) heapFrame </ heap >
                          < form > rev(A) === rev(?C) @ ?B </ form > </ config > */
  while(x != 0) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}



int main()
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > ?H </ heap > < form > TrueFormula </ form > </ config > */
{
  struct nodeList *x;
  struct nodeList *y;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 7;
  x->next = 0;
  /*@ assert < config > < env > x |-> ?x y |-> ?y </ env > < heap > list(?x)([7]) </ heap > < form > TrueFormula </ form > </ config > */
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 6;
  y->next = x;
  x = y;
  /*@ assert < config > < env > x |-> ?x y |-> ?x </ env > < heap > list(?x)([6] @ [7]) </ heap > < form > TrueFormula </ form > </ config > */
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 5;
  y->next = x;
  x = y;
  /*@ assert < config > < env > x |-> ?x y |-> ?x </ env > < heap > list(?x)([5] @ [6] @ [7]) </ heap > < form > TrueFormula </ form > </ config > */
  x = reverse(x) ;
  /*@ assert < config > < env > x |-> ?x y |-> ?y </ env > < heap > list(?x)([7] @ [6] @ [5]) </ heap > < form > TrueFormula </ form > </ config > */
  return 0;
}


/*@ var ?x ?y ?p : ?Int */
/*@ var ?B ?C : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H ?env : ?MapItem */
/*@ var envFrame heapFrame invarFrame : FreeMapItem */