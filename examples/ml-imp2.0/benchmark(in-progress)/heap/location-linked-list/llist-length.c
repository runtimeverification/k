#include <stdlib.h>
#include <stdio.h>

struct nodeLllist {
  struct nodeLllist *next;
};

int length(struct nodeLllist* a)
/*@ pre < config > 
        < env > a |-> a0 </ env >
        < heap > llist(a0)(A) H </ heap > 
        < form > TrueFormula </ form > </ config > */
/*@ post < config > 
         < env > ?rho </ env >
         < heap > llist(a0)(A) H  </ heap > 
         < form > ?l === len(A) /\ returns ?l </ form > </ config > */
{
  int l;
  struct nodeLllist* x;
  if (a==0) l = 0;
  {
    a->next = a->next;
    x = a->next;
    l = 1;
  /*@ invariant < config > 
                < env > a |-> a0  x |-> ?x l |-> ?l </ env >
                < heap > llseg(a0,?x)(?A)  llist(?x)(?X) H </ heap >
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
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > ?H </ heap > < form > TrueFormula </ form > </ config > */
{
  int l;
  struct nodeLllist* x;
  struct nodeLllist* y;
  x = (struct nodeLllist*)malloc(sizeof(struct nodeLllist));
  x->next = 0;
  y = (struct nodeLllist*)malloc(sizeof(struct nodeLllist));
  y->next = x;
  printf("%d %d %d\n", y,y->next,y->next->next);
  l = length(y);
  printf("%d\n",l);
  return 0;
}

/*@ var ?x ?l : ?Int */
/*@ var a0 : FreeInt */
/*@ var ?A ?X : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
