#include <stdlib.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

struct nodeList* prefix(struct nodeList* x, int i)
/*@ pre < config > < env > x |-> ?x i |-> ?i </ env > < heap > list(?x)(A) </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(?x)([?i] @ A) </ heap > < form > returns ?x </ form > </ config > */
{
	struct nodeList* y;
	y = (struct nodeList*) malloc (sizeof(struct nodeList));
	y->val = i;
	y->next = x;
	return y;
}

int main()
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > ?H </ heap > < form > TrueFormula </ form > </ config > */
{
  struct nodeList *x;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 6;
  x->next = 0;
  /*@ assert < config > < env > x |-> ?x </ env > < heap > list(?x)([6]) </ heap > < form > TrueFormula </ form > </ config > */
  x = prefix(x,5) ;
  return 0;
}



/*@ var ?x ?i : ?Int */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
