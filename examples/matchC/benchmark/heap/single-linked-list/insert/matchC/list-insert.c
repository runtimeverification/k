#include <stdlib.h>

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
		if (x->val > i)
		{
			iNode->next = x;
			x = iNode;
		}
		else
		{
			struct nodeList* placement;
			struct nodeList* iterator;
			placement = x->next;
      iterator = placement->next;
/*@ invariant 
    < config > 
    < env > x |-> ?x 
            i |-> ?i
            iNode |-> ?in
            iterator |-> ?it
            placement |-> ?p
    </ env >
    < heap > lseg(?x,?p)(?B)
             ?p |-> ?v1 : (nodeList . val)
             (?p +Int 1) |-> ?it : (nodeList . next)
             ?it |-> ?v2 : (nodeList . val)
             (?it +Int 1) |-> ?aux : (nodeList . next)
             list(?aux)(?C)  
             ?in |-> ?i : (nodeList . val)
             (?in +Int 1) |-> 0 : (nodeList . next)
    </ heap >
    < form > A === (?B @ [?v1] @ [?v2] @ ?C) </ form > </ config > */
			while (iterator!=0)
			{
				if(iterator->val > i)
				{
					iterator = iterator->next;
				}
				else
				{
					placement = iterator;
					iterator = iterator->next;
				}
			}
			iNode->next = placement->next;
			placement->next = iNode;
		}
	}
	return x;
}


int main()
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
  return 0;
}



/*@ var ?x ?y ?it ?i ?in ?aux ?v1 ?v2 ?p : ?Int */
/*@ var ?A ?B ?C ?D : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
