#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* reverse(struct nodeList *x)
/*@ pre  <config> <env> x |-> ?x </env> <heap> list(?x)(A), H </heap>
                  C </config> /\ true */
/*@ post <config> <env> ?rho </env> <heap> list(?x)(rev(A)), H </heap>
                  C </config> /\ returns(?x) */
{
  struct nodeList *p;
  struct nodeList *y;
  p = 0 ;
  /*@ invariant <config> <env> p |-> ?p, x |-> ?x, y |-> ?y </env>
                         <heap> list(?p)(?B), list(?x)(?C), H </heap>
                         C </ config > /\ rev(A) = rev(?C) @ ?B */
  while(x) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}


struct nodeList* append(struct nodeList *x, struct nodeList *y)  
/*@ pre  <config> <env> x |-> ?x, y |-> ?y  </env>
                  <heap> list(?x)(A), list(?y)(B), H </heap>
                  C </ config > /\ true */
/*@ post <config> <env> ?rho </env>
                  <heap> list(?x)(A @ B), H </heap> 
                  C </config> /\ returns(?x) */
{
  struct nodeList *p;
  if (x == 0)
   return y;

  p = x;
  /*@ invariant <config> <env> x |-> ?x, p |-> ?p, !rho </env>
                         <heap>
                           lseg(?x, ?p)(?A1),
                           ?p |-> ?v : nodeList.val,
                           ?p + 1 |-> ?i : nodeList.next,
                           list(?i)(?A2),
                           !H
                         </heap> 
                         C </ config > /\ ?A1 @ [?v] @ ?A2 = A */
  while (p->next)
    p = p->next;
  p->next = y ;

  return x;
}


int length(struct nodeList* x)
/* pre  <config> <env> x |-> x0 </env>
                  <heap> list(x0)(A), H </heap> C </config> /\ true */
/* post <config> < env > ?rho </ env >
                    < heap > list(x0)(A) H </ heap > 
                    < form > returns len(A) </ form > C </ config > */
{
  int l;
  
  l = 0;
  /* invariant < config > < env > x |-> ?x  l |-> len(?A1) </ env >
                           < heap > lseg(x0,?x)(?A1)  list(?x)(?A2) H </ heap >
                           < form > A === (?A1 @ ?A2) </ form >
                           C </ config > */
  while (x) {
    l += 1;
    x = x->next ;
  }

  return l;
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


void destroy(struct nodeList* x)
{
  struct nodeList *y;
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct nodeList* x)
{
  while(x)
  {
    printf("%d ",x->val);
    x = x->next;
  }
  printf("\n"); 
}


/*@ skip */
int main()
{
  struct nodeList *x;
  struct nodeList *y;
  x = create(5);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)([1, 2, 3, 4, 5]) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  x = reverse(x);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > list(?x)([5, 4, 3, 2, 1]) </ heap >
                        < form > TrueFormula </ form > </ config > */
  destroy(x);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > (.).Map </ heap >
                        < form > TrueFormula </ form > </ config > */
  x = create(5);
  printf("x: ");
  print(x);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > list(?x)(!A) </ heap >
                        < form > TrueFormula </ form > </ config > */
  x = reverse(x);
  printf("reverse(x): ");
  print(x);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > list(?x)(rev(!A)) </ heap >
                        < form > TrueFormula </ form > </ config > */
  destroy(x);


  x = create(3);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)([1, 2, 3]) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  y = create(3);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)([1, 2, 3]) list(?y)([1, 2, 3]) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  x = append(x, y);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)([1, 2, 3, 1, 2, 3]) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  destroy(x);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > (.).Map </ heap >
                        < form > TrueFormula </ form > </ config > */
  x = create(3);
  printf("x: ");
  print(x);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)(!A1) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  y = create(3);
  printf("y: "); 
  print(x);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)(!A1) list(?y)(!A2) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  x = append(x, y);
  printf("append(x, y): ");
  print(x);
  /* assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)(!A1 @ !A2) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  destroy(x);
  return 0;
}


/*@ var ?x ?y ?p ?i ?v : ?Int */
/*@ var x0 : FreeInt */
/*@ var ?B ?C ?A1 ?A2 : ?Seq */
/*@ var !A !A1 !A2 : !Seq */
/*@ var A B : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var !rho !H : !MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */
