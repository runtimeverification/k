#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

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

struct nodeList* bubble(struct nodeList* x)
/*@ pre < config >
        < env > x |-> x0 </ env >
        < heap > list(x0)(L) H </ heap >
        < form > ~(x0 === 0) </ form > C 
        </ config > */
/*@ post < config >
         < env > ?rho </ env >
         < heap > list(x0)(?L) H </ heap >
         < form > (seq2mset(L) === seq2mset(?L)) /\ isSorted(?L) </ form > C 
         </ config > */
{
  int change;
  int tmp;
  struct nodeList* p;
  struct nodeList* r;
  if (x != 0)
  {
    change = 1;
/*@ invariant < config >
        < env > x |-> x0 p |-> ?p r |-> ?r change |-> ?c tmp |-> ?t </ env >
        < heap > list(x0)(?L) H </ heap >
        < form >  ~(x0 === 0) /\
                  (seq2mset(L) === seq2mset(?L)) /\
                  (?c === 0 /\ isSorted(?L) \/ ?c === 1)
        </ form > C 
        </ config > */
    while(change == 1)
    {
      change = 0;
      p = x;
      r = x->next;
      
/*@ invariant < config >
        < env > x |-> x0 p |-> ?p r |-> ?r change |-> ?c tmp |-> ?t </ env >
        < heap > lseg(x0,?p)(?L1) 
                 ?p |-> ?v : (nodeList . val)  
                 (?p +Int 1) |-> ?r : (nodeList . next)
                 list(?r)(?L2)
                 H </ heap >
        < form >  ~(x0 === 0) /\
                  (seq2mset(L) === seq2mset(?L)) /\
                  ?L === (?L1 @ [?v] @ ?L2) /\
                  (?c === 0 /\ isSorted(?L1 @ [?v]) \/ ?c === 1)
        </ form > C 
        </ config > */
      while (r != 0)
      {
        if (p->val > r->val)
        {
          change = 1;
          tmp = p->val;
          p->val = r->val;
          r->val = tmp;
        }
        p = r;
        r = r->next;
      }
    }
  }
  return x;
}

void destroy(struct nodeList* x)
{
  struct nodeList *y;
  while(x != 0)
  {
    y = x->next;
    free(x);
    x = y;
  }
}

/*@ verify */
int main()
{
  struct nodeList *x;
  struct nodeList *y;
  x = create(5);
  /*@ assert < config >
             < env > x |-> ?x  y |-> ?y </ env >
             < heap > list(?x)([1,2,3,4,5]) </ heap >
             < form > TrueFormula </ form > </ config > */
  x = bubble(x);
  destroy(x);
  return 0;
}


/*@ var ?x ?y ?p ?r ?t ?c ?v : ?Int */
/*@ var x0 : FreeInt */
/*@ var ?L ?L1 ?L2 : ?Seq */
/*@ var L : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var !rho !H : !MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */
