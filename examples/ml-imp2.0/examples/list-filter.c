struct nodeList {
  int val;
  struct nodeList *next;
};

/*@ var ?x ?y ?p : ?Int */
/*@ var ?B ?C : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */

struct nodeList* filter(struct nodeList* x, int i)
/*@ pre < config > < env > x |-> ?x </ env > < heap > list(?x)(A) </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(?x)(rev(A)) </ heap > < form > returns ?x </ form > </ config > */
{
	struct nodeList* y;
	struct nodeList* z;
	y = x;
	while ((y->val == i) && (y != 0))
	{
		x = y->next;
		free(y);
		y = x;
	}
	z = y;
	y = y->next;
	while(y != 0)
	{
		if(y->val == i)
		{
			z->next = y->next;
			free(y);
			y = z->next;
		}
		else
		{
			z = z->next;
			y = y ->next;
		}
	}
	return x;
}