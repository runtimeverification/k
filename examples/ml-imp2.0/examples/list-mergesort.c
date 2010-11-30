#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};



struct nodeList* split(struct nodeList* p)
/*@ pre  < config > < env > p |-> p0  </ env >
                    < heap > list(p0)(A) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env >  ?rho </ env >
                    < heap > list(p0)(?A1) list(?r)(?A2) H </ heap > 
                    < form > returns ?r /\ (seq2mset(A) === (seq2mset(?A1) U seq2mset(?A2))) </ form > C </ config > */
{
	struct nodeList* r;
  p->next->next = p->next->next;
	if ((p == 0) || (p->next==0)) r = 0;
	else
	{
		r = p->next;
		p->next = r->next;
		r->next = split(p->next);
	}
	return r;
}
//breaker
struct nodeList* merge(struct nodeList* p, struct nodeList* q)
/*@ pre  < config > < env > p |-> p0 q |-> q0 </ env >
                    < heap > list(p0)(A1) list(q0)(A2) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env >  ?rho </ env >
                    < heap > list(?r)(?A) H </ heap > 
                    < form > returns ?r /\ 
                            (seq2mset(?A) === (seq2mset(A1) U seq2mset(A2))) /\ 
                            isSorted(?A) /\ 
                            ((?r === p0) \/ (?r === q0)) </ form > C </ config > */
{
	struct nodeList* t;
  p->next = p->next;
  q->next = q->next;
	if (q==0) t = p;
	else
	{
		if (p==0) t = q;
		else
		{
			if (q->val < p->val)
			{
				t = q;
				q = q->next;
			}
			else
			{
				t = p;
				p = p->next;
			}
			t->next = merge(p,q);
		}
	}
	return t;
}
//breaker
struct nodeList* mergesort(struct nodeList* p)
/*@ pre  < config > < env > p |-> p0  </ env >
                    < heap > list(p0)(A) H </ heap >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env >  ?rho </ env >
                    < heap > list(?r)(?A) H </ heap > 
                    < form > returns ?r /\ (seq2mset(A) === seq2mset(?A)) /\ isSorted(?A) </ form > C </ config > */
{
	struct nodeList* r;
	struct nodeList* q;
  p->next = p->next;
	q = q1 = p1 = NULL;
	if ((p==0) || (p->next == 0)) r = p;
	else
	{
		q = split(p);
		q = mergesort(q);
		p = mergesort(p);
		r = merge(p,q);
	}
	return r;
}
//breaker
void print(struct nodeList* x)
{
	while(x!=0)
	{
		printf("%d ",x->val);
		x = x->next;
	}
	printf("\n");
}
//breaker
int main()
{
	struct nodeList *x;
  struct nodeList *y;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 70;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 6;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 47;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 52;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 5;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 1;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 111;
  y->next = x;
  x = y;
 
	print(x);
	y = split(x);
	print(x);
	print(y);
	x = merge(x,y);
	x = mergesort(x);
	print(x);
	return 0;
}



/*@ var ?r : ?Int */
/*@ var p0 q0 : FreeInt */
/*@ var ?A ?A1 ?A2 : ?Seq */
/*@ var A A1 A2 : FreeSeq */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

