#include <stdlib.h>
#include <stdio.h>

struct nodeDList {
  int val;
  struct nodeDList *next;
  struct nodeDList * prev;
};

struct nodeDList* reverse(struct nodeDList* a)
/*@ pre < config > 
        < env > a |-> a0 </ env >
        < heap > dlseg(a0,b0)(0,0,A) H </ heap > 
        < form > TrueFormula </ form > </ config > */
/*@ post < config > 
         < env > ?rho </ env >
         < heap > dlseg(?a,?b)(0,0,rev(A)) H </ heap > 
         < form > returns ?a </ form > </ config > */
{
  struct nodeDList* p;
  struct nodeDList* aux;
  
  p = 0;
  
  if ((a->next == 0) && (a->prev == 0))
  {
    p = a;
  }
  else
  {
    p = a;
    
    a = a->next;
    a->prev = 0;
    
    p->next = 0;
    p->prev = 0;
  /*@ invariant < config > 
				< env > a |-> a0 x |-> ?x l |-> ?l </ env >
				< heap > 
				  dlseg(a0,?y)(?x,0,?A)  
				  dlseg(?x,b0)(0,?y,?X) 
				  H 
				</ heap >
				< form > (?A @ ?X) === A /\ ?l === len(?A) </ form >
				</ config > */
    while(a!=0)
    {
      aux = a->next;
      a->next = p;
      a->prev = 0;
      p->prev = a;
      p = a;
      a = aux;
    }
  }
  return p;
}

struct nodeDList* insert(struct nodeDList* a, int val)
{
  struct nodeDList* aux;
  aux = (struct nodeDList*)malloc(sizeof(struct nodeDList));
  aux->prev = 0;
  aux->val = val;
  aux->next = a;
  return aux;
}

void print(struct nodeDList* a)
{
  struct nodeDList* aux;
  aux = a;
  printf("\n");
  while(aux!=0)
  {
    printf("%d ", aux->val);
    aux = aux->next;
  }
  printf("\n");
}

int main()
{
  struct nodeDList* x;
  x = (struct nodeDList*)malloc(sizeof(struct nodeDList));
  x->val = 5;
  x->next = 0;
  x->prev = 0;
  print(x);
  x = insert(x,7);
  x = insert(x,10);
  x = insert(x,8);
  print(x);
  x = reverse(x);
  print(x);
  return 0;
}


/*@ var ?x ?l ?y ?z : ?Int */
/*@ var a0 b0 : FreeInt */
/*@ var ?A ?X : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
