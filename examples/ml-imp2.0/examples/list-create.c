#include <stdlib.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

struct nodeList* create()
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(?x)([5] @ [6] @ [7]) </ heap > < form > returns ?x </ form > </ config > */
{
  struct nodeList *x;
  struct nodeList *y;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 7;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 6;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 5;
  y->next = x;
  x = y;
  return x;
}

int main()
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > ?H </ heap > < form > TrueFormula </ form > </ config > */
{
  struct nodeList *x;
  x = create();
  return 0;
}


/*@ var ?x ?y : ?Int */
/*@ var ?A : ?Seq */
/*@ var ?rho ?H : ?MapItem */
