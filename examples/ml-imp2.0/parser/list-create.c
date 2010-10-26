struct nodeList {
  int val;
  struct nodeList *next;
};

/*@ var ?x ?y : ?Int */
/*@ var ?A : ?Seq */
/*@ var ?rho ?H : ?MapItem */

void main()
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > ?H </ heap > < form > TrueFormula </ form > </ config > */
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
/*@ assert < config > < env > x |-> ?x y |-> ?y </ env > < heap > list(?x)([5] @ [6] @ [7]) </ heap > < form > TrueFormula </ form > </ config > */
}
