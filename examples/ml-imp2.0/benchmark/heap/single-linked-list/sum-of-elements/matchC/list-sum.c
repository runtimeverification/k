#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

int summ(struct nodeList* a)
/*@ pre < config > 
        < env > a |-> a0 </ env >
        < heap > list(a0)(A) H </ heap > 
        < form > TrueFormula </ form > </ config > */
/*@ post < config > 
         < env > ?rho </ env >
         < heap > ?H </ heap > 
         < form > ?sum === sum(A) /\ returns ?sum </ form > </ config > */
{
  int s;
  struct nodeList* x;
  x = a;
  s = 0;
/*@ invariant < config > 
              < env > a |-> a0  x |-> ?x s |-> ?sum </ env >
              < heap > lseg(a0,?x)(?A)  list(?x)(?X) H </ heap >
              < form > (?A @ ?X) === A /\ ((?sum) === sum(?A)) </ form >
              </ config > */
  while (x != 0) {
    s = s + x->val;
    x = x->next;
  }
  return s;
}

int main()
{
  struct nodeList* x;
  struct nodeList* y;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 5;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 4;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 3;
  y->next = x;
  x = y;
  summ(x);
  printf("%d\n", summ(x));
  return 0;
}

/*@ var ?x ?sum : ?Int */
/*@ var a0 : FreeInt */
/*@ var ?A ?X : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
