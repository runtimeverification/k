#include <stdlib.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* append(struct nodeList *x, struct nodeList *y)  
/*@ pre < config >
         < env > x |-> ?x  y |-> ?y  </ env >
         < heap > list(?x)(A) list(?y)(B) ?H </ heap >
         < form > TrueFormula </ form >
         </ config > */
/*@ post < config > 
          < env >  ?rho </ env >
          < heap > list(?x)(A @ B) ?H </ heap > 
          < form > returns ?x </ form > 
          </ config > */
{
  struct nodeList *p;
  struct nodeList *i;
  if (x == 0) x = y;
  else
  {
    p = x ;
    i = x->next; 
/*@ invariant < config > 
         < env > x |-> ?x  y |-> ?y  i |-> ?i  p |-> ?p  </ env >
         < heap > lseg(?x , ?p)(?A) 
                  ?p |-> ?v : (nodeList . val)
                  (?p +Int 1) |-> ?i :  (nodeList . next)
                  list(?i)(?B)  
                  list(?y)(B) 
                  ?H
         </ heap > 
         < form > (?A @ [?v] @ ?B) === A </ form > 
         </ config > */
    while (i != 0)
    {
        p = i ;
        i = i->next;
    }
    p->next = y ;
  }
  return x;
}

int main()
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > ?H </ heap > < form > TrueFormula </ form > </ config > */
{
  struct nodeList* x;
  struct nodeList* y;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 5;
  x->next = 0;
  
/*@ assert < config > 
           < env > x |-> ?x y |-> ?y </ env > 
           < heap > list(?x)(!A) </ heap > 
           < form > TrueFormula </ form > </ config > */
           
  
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 6;
  y->next = 0;

/*@ assert < config > 
           < env > x |-> ?x y |-> ?y </ env > 
           < heap > list(?x)(!A) list(?y)(!B) </ heap > 
           < form > TrueFormula </ form > </ config > */
  x = append(x,y);
/*@ assert < config > 
           < env > x |-> ?x y |-> ?y </ env > 
           < heap > list(?x)(?A) ?H </ heap > 
           < form > ?A === (!A @ !B) </ form > </ config > */
  return 0;
}

/*@ var ?x ?y ?p ?i ?v : ?Int */
/*@ var ?A ?B : ?Seq */
/*@ var !A !B : !Seq */
/*@ var A B : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
