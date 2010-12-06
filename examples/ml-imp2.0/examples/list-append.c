#include <stdlib.h>
#include <stdio.h>

struct nodeList {
 int val;
 struct nodeList *next;
};

struct nodeList* append(struct nodeList* x, struct nodeList y)
/*@ pre < config > < env > x |-> ?x y |-> ?y </ env >
          < heap > list(?x)(A) list(?y)(B) H </ heap >
          < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
          < heap > list(?p)(?A) H </ heap > 
          < form > returns ?p /\ (?A === A @ B) </ form > C </ config > */
{
  struct nodeList *p;
  struct nodeList *i;
  p = 0;
  if (x!=0)
  {
    i = x->next;
    p = x;
/*@ invariant < config > < env > x |-> ?x y |-> ?y i |-> ?i p |-> ?p </ env >
          < heap > lseg(?x,?p)(?A1) ?p |-> ?v : (nodeList . val) (?p +Int 1) |-> ?i : (nodeList . next) list(?i)(?A2) list(?y)(B) H </ heap > 
          < form > (A === (?A1 @ [?v] @ ?A2)) </ form > C </ config > */
    while(i!=0)
    {
      p=i;
      i = i->next;
    }
    p->next = y;
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
  y->val = 98;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 5;
  y->next = x;
  x = y;
  /*@ assert < config > 
             < env > x |-> ?x  y |-> ?x </ env > 
             < heap > list(?x)([5, 6, 7]) </ heap > 
             < form > TrueFormula </ form > </ config > */
  printf("x: %d %d %d\n",x->val, x->next->val, x->next->next->val);
  x = append(x,x);
  printf("x: %d %d %d\n",x->val, x->next->val, x->next->next->val);
 return 0;
}




/*@ var ?x ?y ?l ?i ?p ?v : ?Int */
/*@ var l0 : FreeInt */
/*@ var ?A ?A1 ?A2 : ?Seq */
/*@ var A B : FreeSeq */
/*@ var !rho !H : !MapItem */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

