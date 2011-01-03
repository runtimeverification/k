struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* filter(struct nodeList* x, int i)
/*@ pre < config > < env > x |-> ?x i |-> i0 </ env > < heap > list(?x)(A) </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(?x)(?A) </ heap > < form > returns ?x /\ ~(contain(?A, i0)) </ form > </ config > */
{
	struct nodeList* y;
	struct nodeList* z;
	y = x;
  
/*@ invariant < config > 
              < env > x |-> ?x y |-> ?x z |-> 0 i |-> i0 </ env > 
              < heap > list(?x)(A) </ heap > 
              < form > TrueFormula </ form > 
              </ config > */
	while ((y->val == i) && (y != 0))
	{
		x = y->next;
		free(y);
		y = x;
	}
	z = y;
	y = y->next;
  
/*@ invariant < config > 
              < env > x |-> ?x y |-> ?y z |-> ?z i |-> i0 </ env > 
              < heap > 
                  lseg(?x,?z)(?A) 
                  ?z |-> ?v : (nodeList . val)
                  (?z +Int 1) |-> ?y : (nodeList . next)
                  list(?y)(?B)
              </ heap > 
              < form > ~(contain(?A, i0)) /\ ~(?v === i0) /\ ~(?z === 0) </ form > </ config >  */
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
			z = y;
			y = y ->next;
		}
	}
	return x;
}


/*@ var ?x ?y ?z ?v : ?Int */
/*@ var i0 : FreeInt */
/*@ var ?A ?B ?C : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
