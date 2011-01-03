#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* append(struct nodeList *x, struct nodeList *y)  
/*@ pre  < config > < env > x |-> ?x  y |-> ?y  </ env >
                    < heap > list(?x)(A) list(?y)(B) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env >  ?rho </ env >
                    < heap > list(?x)(A @ B) H </ heap > 
                    < form > returns ?x </ form > C </ config > */
{
  struct nodeList *p;
  struct nodeList *i;
  if (x == 0) x = y;
  else
  {
    i = x->next;
    p = x;
/*@ invariant < config > < env > x |-> ?x y |-> ?y i |-> ?i p |-> ?p </ env >
          < heap > lseg(?x,?p)(?A1) ?p |-> ?v : (nodeList . val) (?p +Int 1) |-> ?i : (nodeList . next) list(?i)(?A2) list(?y)(B) H </ heap > 
          < form > (A === (?A1 @ [?v] @ ?A2)) </ form > C </ config > */
    while(i!=0)
    {
        p = i ;
        i = i->next;
    }
    p->next = y ;
  }
  return x;
}

struct nodeList* quicksort(struct nodeList* l)
/*@ pre  < config > < env > l |-> l0 </ env >
                    < heap > list(l0)(A) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env >  ?rho </ env >
                    < heap > list(?l)(?A) H </ heap > 
                    < form > returns l0 </ form > C </ config > */
{
  struct nodeList* a;
  struct nodeList* b;
  struct nodeList* p;
  struct nodeList* x;
  struct nodeList* y;
  if (l!=0)
  {
    l->next = l->next;
    p=l;
    x=l->next;
/*@ assert < config > 
   < env > p |-> ?p x |-> ?x y |-> ?y a |-> ?a b |-> ?b l |-> l0 </ env >
   < heap > ?p |-> ?v : (nodeList . val) (?p +Int 1) |-> ?x : (nodeList . next) 
            list(?x)(?C) </ heap >
   < form > (A === [?v] @ ?C)  </ form > 
   </ config >
*/
    p->next=0;
    a=0;
    b=0;

/*@ invariant < config > 
   < env > l |-> ?l p |-> ?p x |-> ?x y |-> ?y a |-> ?a b |-> ?b </ env >
   < heap > ?p |-> ?v : (nodeList . val) (?p +Int 1) |-> 0 : (nodeList . next) 
            list(?a)(?A) 
            list(?b)(?B) 
            list(?x)(?C) </ heap >
   < form > (seq2mset(A) === {| ?v |} U seq2mset(?A) U seq2mset(?B) U seq2mset(?C))  </ form > 
   </ config >
*/
    while (x != 0)
    {
     y = x;
     x = x->next;
     if (y->val > p->val)
     {
      y->next = b;
      b = y;
     }
     else
     {
      y->next = a;
      a = y;
     }
    }
    a = quicksort(a);
    b = quicksort(b);
    l = append(a,p);
    l = append(l,b);
  }
  return l;
}

int main()
{
  struct nodeList *x;
  struct nodeList *y;
  struct nodeList *z;
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
             < env > x |-> ?x  y |-> ?x  z |-> ?z </ env > 
             < heap > list(?x)([5, 6, 7]) </ heap > 
             < form > TrueFormula </ form > </ config > */
  printf("x: %d %d %d\n",x->val, x->next->val, x->next->next->val);
  z = (struct nodeList*)malloc(sizeof(struct nodeList));
  z->val = 5;
  z->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 3;
  y->next = z;
  z = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 1;
  y->next = z;
  z = y;
  printf("z: %d %d %d\n",z->val, z->next->val, z->next->next->val);
  /*@ assert < config > 
             < env > x |-> ?x  z |-> ?z  y |-> ?z </ env > 
             < heap > list(?x)([5, 6, 7]) list(?z)([1, 3, 5]) </ heap > 
             < form > TrueFormula </ form > </ config > */
  x = append(x,z);
  printf("x: %d %d %d %d %d %d\n",x->val, x->next->val, x->next->next->val, x->next->next->next->val, x->next->next->next->next->val, x->next->next->next->next->next->val);
  /*@ assert < config > 
             < env > x |-> ?x  z |-> ?z  y |-> ?z </ env > 
             < heap > list(?x)([5, 6, 7, 1, 3, 5]) </ heap > 
             < form > TrueFormula </ form > </ config > */
  x = quicksort(x);
  return 0;
}

/*@ var ?x ?y ?p ?i ?v ?z ?l ?a ?b : ?Int */
/*@ var l0 : FreeInt */
/*@ var ?A ?A1 ?A2 ?B ?C : ?Seq */
/*@ var !A1 !A2 : !Seq */
/*@ var A B L : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var !rho !H : !MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */
