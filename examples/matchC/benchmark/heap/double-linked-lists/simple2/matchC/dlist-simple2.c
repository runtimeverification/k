#include <stdlib.h>

struct nodeDList {
  int val;
  struct nodeDList *next;
  struct nodeDList * prev;
};

int length(struct nodeDList* a)
/*@ pre < config > 
        < env > a |-> a0 </ env >
        < heap > dlist(a0,b0)(A) H </ heap > 
        < form > ~(a0 === 0) </ form > </ config > */
/*@ post < config > 
         < env > ?rho </ env >
         < heap > dlist(a0,b0)(A) H </ heap > 
         < form > returns ?l </ form > </ config > */
{
  int l;
  struct nodeDList* x;
  x = a->next;
  l = 1;
  
/*@ assert < config > 
              < env > a |-> a0  x |-> ?x l |-> ?l </ env >
              < heap > 
                dlseg(a0,a0)(?x,0,?A)  
                dlseg(?x,b0)(0,a0,?X) 
                H 
              </ heap >
              < form > ~(a0 === 0) /\ (A === ?A @ ?X) /\ (?l === len(?A)) </ form >
              </ config > */
/*@ assert < config > 
              < env > a |-> a0 x |-> ?x l |-> ?l </ env >
              < heap > 
                dlseg(a0,b0)(0,0,A) 
                H 
              </ heap >
              < form > ~(a0 === 0) </ form >
              </ config > */
  return l;
}

/*@ var ?x ?l ?y : ?Int */
/*@ var a0 b0 : FreeInt */
/*@ var ?A ?X : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
