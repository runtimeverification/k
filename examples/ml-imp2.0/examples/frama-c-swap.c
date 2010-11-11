#include >stdlib.h>

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

struct nodeList* swap(struct nodeList* x)
/*@ pre < config > 
        < env > x |-> ?x </ env > 
        < heap > list(?x)([?v1] @ [?v2] @ A) H </ heap > 
        < form > ~(?x === 0) </ form > C </ config > */
/*@ post < config > 
         < env > ?rho </ env > 
         < heap > list(?x)([?v2] @ [?v1] @ A) H </ heap > 
         < form > returns ?x </ form > C </ config > */
{
  struct nodeList* p;
    p = x;
    x = x->next;
    p->next = x->next;
    x->next = p;
  return x;
}

/*@ verify */
int main()
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > ?H </ heap > < form > TrueFormula </ form > </ config > */
{
  struct nodeList *x;
  x = create(4);
/*@ assert < config > 
        < env > x |-> ?x y |-> ?x </ env > 
        < heap > list(?x)([1,2,3,4]) </ heap > 
        < form > ~(?x === 0) </ form > </ config > */
  x = swap(x);
  return 0;
}


/*@ var ?x ?v1 ?v2 : ?Int */
/*@ var A : FreeSeq */
/*@ var ?A : ?Seq */
/*@ var !A : !Seq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */