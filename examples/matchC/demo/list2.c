#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* reverse(struct listNode *x)
{
  struct listNode *p;
  struct listNode *y;
  p = 0 ;
  while(x) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}


struct listNode* append(struct listNode *x, struct listNode *y)  
{
  struct listNode *p;
  if (x == 0)
   return y;

  p = x;
  while (p->next)
    p = p->next;
  p->next = y ;

  return x;
}


int length(struct listNode* x)
{
  int l;
  
  l = 0;
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
