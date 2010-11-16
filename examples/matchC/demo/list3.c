#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* reverse(struct listNode *x)
/*@ pre  < config > < env > x |-> ?x </ env > < heap > list(?x)(A) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(?x)(rev(A)) H </ heap >
                    < form > returns ?x </ form > C </ config > */
{
  struct listNode *p;
  struct listNode *y;
  p = 0 ;
  /*@ invariant < config > < env > p |-> ?p  x |-> ?x  y |-> ?y </ env >
                           < heap > list(?p)(?B)  list(?x)(?C) H </ heap >
                           < form > rev(A) === rev(?C) @ ?B </ form >
                           C </ config > */
  while(x) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}


struct listNode* append(struct listNode *x, struct listNode *y)  
/*@ pre  < config > < env > x |-> ?x  y |-> ?y  </ env >
                    < heap > list(?x)(A)  list(?y)(B) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env >  ?rho </ env >
                    < heap > list(?x)(A @ B) H </ heap > 
                    < form > returns ?x </ form > C </ config > */
{
  struct listNode *p;
  if (x == 0)
   return y;

  p = x;
  /*@ invariant < config > < env > x |-> ?x  p |-> ?p  !rho </ env >
                           < heap >
                             lseg(?x , ?p)(?A1) 
                             ?p |-> ?v : (listNode . val)
                             (?p +Int 1) |-> ?i : (listNode . next)
                              list(?i)(?A2)  
                             !H
                           </ heap > 
                           < form > (?A1 @ [?v] @ ?A2) === A </ form > 
                           C </ config > */
  while (p->next)
    p = p->next;
  p->next = y ;

  return x;
}


int length(struct listNode* x)
/*@ pre  < config > < env > x |-> x0 </ env >
                    < heap > list(x0)(A) H </ heap > 
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > list(x0)(A) H </ heap > 
                    < form > returns len(A) </ form > C </ config > */
{
  int l;
  
  l = 0;
  /*@ invariant < config > < env > x |-> ?x  l |-> len(?A1) </ env >
                           < heap > lseg(x0,?x)(?A1)  list(?x)(?A2) H </ heap >
                           < form > A === (?A1 @ ?A2) </ form >
                           C </ config > */
  while (x) {
    l += 1;
    x = x->next ;
  }

  return l;
}


struct listNode* create(int n)
{
  struct listNode *x;
  struct listNode *y;
  x = 0;
  while (n)
  {
    y = x;
    x = (struct listNode*)malloc(sizeof(struct listNode));
    x->val = n;
    x->next = y;
    n -= 1;
  }
  return x;
}


void destroy(struct listNode* x)
{
  struct listNode *y;
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct listNode* x)
{
  while(x)
  {
    printf("%d ",x->val);
    x = x->next;
  }
  printf("\n"); 
}


int main()
{
  struct listNode *x;
  struct listNode *y;
  x = create(5);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)([1, 2, 3, 4, 5]) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  x = reverse(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > list(?x)([5, 4, 3, 2, 1]) </ heap >
                        < form > TrueFormula </ form > </ config > */
  destroy(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > (.).Map </ heap >
                        < form > TrueFormula </ form > </ config > */
  x = create(5);
  printf("x: ");
  print(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > list(?x)(!A) </ heap >
                        < form > TrueFormula </ form > </ config > */
  x = reverse(x);
  printf("reverse(x): ");
  print(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > list(?x)(rev(!A)) </ heap >
                        < form > TrueFormula </ form > </ config > */
  destroy(x);


  x = create(3);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)([1, 2, 3]) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  y = create(3);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)([1, 2, 3]) list(?y)([1, 2, 3]) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  x = append(x, y);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)([1, 2, 3, 1, 2, 3]) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  destroy(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > (.).Map </ heap >
                        < form > TrueFormula </ form > </ config > */
  x = create(3);
  printf("x: ");
  print(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)(!A1) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  y = create(3);
  printf("y: "); 
  print(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env > 
                        < heap > list(?x)(!A1) list(?y)(!A2) </ heap > 
                        < form > TrueFormula </ form > </ config > */
  x = append(x, y);
  printf("append(x, y): ");
  print(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env > 
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
