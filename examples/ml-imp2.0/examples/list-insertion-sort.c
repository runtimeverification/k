#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* insertionSort(struct nodeList* l)
/*@ pre < config >
        < env > l |-> l0 </ env >
        < heap > list(l0)(L) H </ heap >
        < form > TrueFormula </ form > C 
        </ config > */
/*@ post < config >
         < env > ?rho </ env >
         < heap > list(l0)(?L) H </ heap >
         < form > returns l0 /\ (seq2mset(L) === seq2mset(?L)) /\ isSorted(?L) </ form > C 
         </ config > */
{
  struct nodeList* x;
  struct nodeList* e;
  struct nodeList* y;
  x = l;
  l = 0;
/*@ invariant < config >
         < env > l |-> ?l x |-> ?x y |-> ?y e |-> ?e </ env >
         < heap > list(?l)(?L) list (?x)(?X) H </ heap >
         < form > (seq2mset(L) === seq2mset(?L) U seq2mset(?X)) /\
                  isSorted(?L) 
         </ form > C 
         </ config > */
  while(x != 0)
  {
    e = x;
    x = x->next;
    if (l != 0)
    {
      if(e->val > l->val)
      {
        y = l;
/*@ invariant < config >
         < env > l |-> ?l x |-> ?x y |-> ?y e |-> ?e </ env >
         < heap > lseg(?l,?y)(?A)
                  ?y |-> ?u : (nodeList . val)
                  (?y +Int 1) |-> ?n : (nodeList . next)
                  list(?n)(?B)
                  ?e |-> ?v : (nodeList . val)
                  (?e +Int 1) |-> ?x : (nodeList . next)
                   list(?x)(?X)
         H </ heap >
         < form > (seq2mset(L) === seq2mset(?L) U seq2mset([?v] @ ?X)) /\
                  isSorted(?L) /\ (?L === (?A @ [?u] @ ?B)) /\ @(max(seq2mset(?A) U {| ?u |}) <Int ?v)
         </ form > C 
         </ config > */
        while ((y->next != 0) && (e->val > y->next->val))
        {
          y = y->next;
        }
        e->next = y->next;
        y->next = e;
      }
      else
      {
        e->next = l;
        l = e ;
      }
    }
    else
    {
      e->next = 0;
      l = e ;
    }
  }
  return l;
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

int main()
{
  struct nodeList *x;
  struct nodeList *y;
  x = create(5);
  x->val = 10;
  print(x);
  x = insertionSort(x);
  print(x);
  return 0;
}


/*@ var ?a ?b ?h ?t ?e ?n ?u ?v ?l ?x ?y ?s : ?Int */
/*@ var x0 l0 : FreeInt */
/*@ var ?A ?A' ?B ?B' ?C ?L ?X : ?Seq */
/*@ var L A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */
