#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

struct nodeList* swap(struct nodeList* x)
/*@ pre < config > 
             < env > x |-> x0 </ env > 
             < heap > list(x0)([v1] @ [v2] @ A) H </ heap > 
             < form > ~(x0 === 0) </ form > C </ config > */
/*@ post < config > 
             < env > ?rho </ env > 
             < heap > list(?x)([v2] @ [v1] @ A) H </ heap > 
             < form > returns ?x </ form > C </ config > */
{
  struct nodeList* p;
  p = x;
  x = x->next;
  p->next = x->next;
  x->next = p;
  return x;
}

struct nodeList* create(int n)
{
  struct nodeList *x;
  struct nodeList *y;
  x = 0;
  while (n)
  {
    y = x;
    x = (struct nodeList*)malloc(sizeof(struct nodeList));
    x->val = n;
    x->next = y;
    n -= 1;
  }
  return x;
}

struct nodeList* print(struct nodeList* x)
/*@ pre < config > 
             < env > x |-> x0 </ env > 
             < heap > list(x0)(A) H </ heap > 
             < form > TrueFormula </ form > C </ config > */
/*@ post < config > 
             < env > ?rho </ env > 
             < heap > list(x0)(A) H </ heap > 
             < form > returns x0 </ form > C </ config > */
{
  struct nodeList* smth;
  smth = x;
/*@ invariant < config > 
             < env > x |-> x0  smth |-> ?s </ env > 
             < heap > lseg(x0,?s)(?A) list(?s)(?A') H </ heap > 
             < form > A === ?A @ ?A' </ form > C </ config > */
  while(smth != 0)
  {
    printf("%d ", smth->val);
    smth = smth->next;
  }
  printf("\n");
  return x;
}

/*@ verify */
int main()
{
  struct nodeList *x;
  struct nodeList *y;
  x = create(5);
  // /*@ assert < config > 
             // < env > x |-> ?x  y |-> ?x </ env > 
             // < heap > list(?x)([1, 2, 3, 4, 5]) </ heap > 
             // < form > TrueFormula </ form > </ config > */
  print(x);
  x->next = x->next;
  x->next->next = x->next->next;
  x = swap(x);
  print(x);
  
  return 0;
}


/*@ var ?x ?y ?p ?i ?v ?s : ?Int */
/*@ var x0 v0 v1 v2 : FreeInt */
/*@ var !v1 !v2 : !Int */
/*@ var ?B ?C ?A1 ?A2 ?A ?A' : ?Seq */
/*@ var !A !A1 !A2 : !Seq */
/*@ var A B : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var !rho !H : !MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */
