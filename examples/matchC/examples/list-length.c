#include <stdlib.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

int length(struct nodeList* a)
/*@ pre < config > 
        < env > a |-> a0 </ env >
        < heap > list(a0)(A) H </ heap > 
        < form > TrueFormula </ form > C </ config > */
/*@ post < config > 
         < env > ?rho </ env >
         < heap > ?H </ heap > 
         < form > ?l === len(A) /\ returns ?l </ form > C </ config > */
{
  int l;
  struct nodeList* x;
  x = a;
  l = 0;
/*@ invariant < config > 
              < env > a |-> a0  x |-> ?x l |-> ?l </ env >
              < heap > lseg(a0,?x)(?A)  list(?x)(?X) H </ heap >
              < form > (?A @ ?X) === A /\ ?l === len(?A) </ form >
              C </ config > */
  while (x != 0) {
        x = x->next ;
        l = l + 1 ;
    }
  return l;
}

int main()
{
  int l;
  struct nodeList* x;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 5;
  x->next = 0;
  l = length(x);
  printf("%d ", l);
  printf("\n");
  return 0;
}

/*@ var ?x ?l : ?Int */
/*@ var a0 : FreeInt */
/*@ var ?A ?X : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

