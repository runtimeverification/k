#include <stdlib.h>

struct nodeDList {
  int val;
  struct nodeDList *next;
  struct nodeDList * prev;
};

/*@ verify */
int main()
{
  struct nodeDList* x;
  x = (struct nodeDList*)malloc(sizeof(struct nodeDList));
  x->val = 5;
  x->next = 0;
  x->prev = 0;
/*@ assert 
  < config >
  < env > x |-> ?x </ env >
  < heap >  ?x |-> 5 : (nodeDList . val) (1 +Int ?x) |-> 0 : (
    nodeDList . next) (2 +Int ?x) |-> 0 : (nodeDList . prev) </ heap >
  < form > TrueFormula </ form >
  </ config >
  */
/*@ assert 
  < config >
  < env > x |-> ?x </ env >
  < heap >  dlseg(?x,?x)(0,0,[5]) </ heap >
  < form > TrueFormula </ form >
  </ config >
  */
/*@ assert 
  < config >
  < env > x |-> ?x </ env >
  < heap >  dlist(?x,?x)([5]) </ heap >
  < form > TrueFormula </ form >
  </ config >
  */
}

/*@ var ?x ?l ?y : ?Int */
/*@ var a0 b0 : FreeInt */
/*@ var ?A ?X : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
