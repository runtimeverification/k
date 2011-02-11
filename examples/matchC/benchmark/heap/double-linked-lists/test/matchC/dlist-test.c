#include <stdlib.h>
#include <stdio.h>

struct nodeDList {
  int val;
  struct nodeDList *next;
  struct nodeDList * prev;
};

int length(struct nodeDList* a)
/*@ pre < config > 
        < env > a |-> a0 </ env >
        < heap > dlseg(a0,b0)(0,0,A) H </ heap > 
        < form > TrueFormula </ form > </ config > */
/*@ post < config > 
         < env > ?rho </ env >
         < heap > dlseg(a0,b0)(0,0,A) H </ heap > 
         < form > ?l === len(A) /\ returns ?l </ form > </ config > */
{
  int l;
  struct nodeDList* x;
  l = 0;
  if (a != 0)
  {             
  x = a;
  /*@ invariant < config > 
				< env > a |-> a0 x |-> ?x l |-> ?l </ env >
				< heap > 
				  dlseg(a0,?y)(?x,0,?A)  
				  dlseg(?x,b0)(0,?y,?X) 
				  H 
				</ heap >
				< form > (?A @ ?X) === A /\ ?l === len(?A) </ form >
				</ config > */
	while (x != 0) {
		  x = x->next ;
		  l = l + 1 ;
	  }
  }
  return l;
}

int main()
{
  struct nodeDList* x;
  x = (struct nodeDList*)malloc(sizeof(struct nodeDList));
  x->val = 5;
  x->next = 0;
  x->prev = 0;
  printf("%d\n", length(x));
  return 0;
}


/*@ var ?x ?l ?y ?z : ?Int */
/*@ var a0 b0 : FreeInt */
/*@ var ?A ?X : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
