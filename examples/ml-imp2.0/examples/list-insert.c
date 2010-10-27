struct nodeList {
  int val;
  struct nodeList *next;
};

struct nodeList* insert(struct nodeList* x, int i)
/*@ pre < config > < env > x |-> ?x i |-> ?i </ env > < heap > list(?x)(A) </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(?x)(?A) </ heap > < form > returns ?x /\ (seq2mset(?A) === seq2mset(A @ [?i])) </ form > </ config > */
{
	struct nodeList* iNode;
	iNode = (struct nodeList*) malloc (sizeof(struct nodeList));
	iNode->val = i;
	iNode->next = 0;
	if (x == 0) x = iNode;
	else
	{
		struct nodeList* iterator;
		iterator = x;
/*@ invariant < config > 
              < env > x |-> ?x 
                      iterator |-> ?iterator
                      iNode |-> ?iNode
                      i |-> ?i
              </ env >
              < heap > lseg(?x,?iterator)(?B)
                       list(?iterator)(?C)  
                       ?iNode |-> ?i : (nodeList . val)
                       (?iNode +Int 1) |-> 0 : (nodeList . next)
              </ heap >
              < form > A === (?B @ ?C) </ form > </ config > */
		while ((iterator!=0) && (iterator->val < i))
		{
			iterator = iterator->next;
		}
		iNode->next = iterator->next;
		iterator->next = iNode;
	}
	return x;
}


void main()
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > ?H </ heap > < form > TrueFormula </ form > </ config > */
{
  struct nodeList *x;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 5;
  x->next = 0;
  /*@ assert < config > < env > x |-> ?x </ env > < heap > list(?x)([5]) </ heap > < form > TrueFormula </ form > </ config > */
  x = insert(x,8) ;
  x = insert(x,3) ;
}



/*@ var ?x ?y ?iterator ?i ?iNode ?aux ?v : ?Int */
/*@ var ?A ?B ?C ?D : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */