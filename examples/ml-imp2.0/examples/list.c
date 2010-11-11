#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* reverse(struct nodeList *x)
/*@ pre  < config > < env > x |-> ?x </ env > < heap > list(?x)(A) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(?x)(rev(A)) H </ heap >
                    < form > returns ?x </ form > C </ config > */
{
  struct nodeList *p;
  struct nodeList *y;
  p = 0 ;
  /*@ invariant < config > < env > p |-> ?p  x |-> ?x  y |-> ?y </ env >
                           < heap > list(?p)(?B) list(?x)(?C) H </ heap >
                           < form > rev(A) === rev(?C) @ ?B </ form >
                           C </ config > */
  while(x != 0) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}


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
    p = x ;
    i = x->next; 
    /*@ invariant < config > < env > x |-> ?x  i |-> ?i  p |-> ?p  !rho </ env >
                             < heap >
                               lseg(?x , ?p)(?A1) 
                               ?p |-> ?v : (nodeList . val)
                               (?p +Int 1) |-> ?i : (nodeList . next)
                                list(?i)(?A2)  
                               !H
                             </ heap > 
                             < form > (?A1 @ [?v] @ ?A2) === A </ form > 
                             C </ config > */
    while (i != 0)
    {
        p = i ;
        i = i->next;
    }
    p->next = y ;
  }
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
  x = reverse(x);
  print(x);
  /*@ assert < config >
             < env > x |-> ?x  y |-> ?y </ env >
             < heap > list(?x)([5, 4, 3, 2, 1]) </ heap >
             < form > TrueFormula </ form > </ config > */
  destroy(x);
  /*@ assert < config >
             < env > x |-> ?x  y |-> ?y </ env >
             < heap > (.).Map </ heap >
             < form > TrueFormula </ form > </ config > */
  x = create(5);
  print(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > list(?x)(!A) </ heap >
                        < form > TrueFormula </ form > </ config > */
  x = reverse(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > list(?x)(rev(!A)) </ heap >
                        < form > TrueFormula </ form > </ config > */
  destroy(x);


  x = create(3);
  // /*@ assert < config > 
             // < env > x |-> ?x  y |-> ?y </ env > 
             // < heap > list(?x)([1, 2, 3]) </ heap > 
             // < form > TrueFormula </ form > </ config > */
  y = create(3);
  // /*@ assert < config > 
             // < env > x |-> ?x  y |-> ?y </ env > 
             // < heap > list(?x)([1, 2, 3]) list(?y)([1, 2, 3]) </ heap > 
             // < form > TrueFormula </ form > </ config > */
  x = append(x, y);
  /*@ assert < config > 
             < env > x |-> ?x  y |-> ?y </ env > 
             < heap > list(?x)([1, 2, 3, 1, 2, 3]) </ heap > 
             < form > TrueFormula </ form > </ config > */
  destroy(x);
  /*@ assert < config > < env > x |-> ?x  y |-> ?y </ env >
                        < heap > (.).Map </ heap >
                        < form > TrueFormula </ form > </ config > */
  x = create(3);
  printf("x: %d %d %d\n",x->val, x->next->val, x->next->next->val);
  /*@ assert < config > 
             < env > x |-> ?x  y |-> ?y </ env > 
             < heap > list(?x)(!A1) </ heap > 
             < form > TrueFormula </ form > </ config > */
  y = create(3);
  printf("y: %d %d %d\n",y->val, y->next->val, y->next->next->val);
  /*@ assert < config > 
             < env > x |-> ?x  y |-> ?y </ env > 
             < heap > list(?x)(!A1) list(?y)(!A2) </ heap > 
             < form > TrueFormula </ form > </ config > */
  x = append(x, y);
  printf("append(x, y): %d %d %d %d %d %d\n",x->val, x->next->val, x->next->next->val, x->next->next->next->val, x->next->next->next->next->val, x->next->next->next->next->next->val);
  /*@ assert < config > 
             < env > x |-> ?x  y |-> ?y </ env > 
             < heap > list(?x)(!A1 @ !A2) </ heap > 
             < form > TrueFormula </ form > </ config > */
  destroy(x);
  return 0;
}


/*@ var ?x ?y ?p ?i ?v ?s : ?Int */
/*@ var x0 : FreeInt */
/*@ var ?B ?C ?A1 ?A2 ?A ?A' : ?Seq */
/*@ var !A !A1 !A2 : !Seq */
/*@ var A B : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var !rho !H : !MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */
