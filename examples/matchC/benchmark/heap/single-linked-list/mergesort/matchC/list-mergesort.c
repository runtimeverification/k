#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};



struct listNode* split(struct listNode* p)
/*@ cfg <heap> list(p0)(A) => list(p0)(?A1), list(r)(?A2) </heap>
    req p = p0 
    ens returns(r) /\ (seq2mset(A) = (seq2mset(?A1) U seq2mset(?A2))) */
{
	struct listNode* r;
	if ((p == 0) || (p->next==0)) r = 0;
	else
	{
    p->next->next = p->next->next;
		r = p->next;
		p->next = r->next;
		r->next = split(p->next);
	}
	return r;
}


struct listNode* merge(struct listNode* p, struct listNode* q)
/*@ cfg <heap> list(p)(A1), list(q)(A2) => list(r)(?A) </heap>
    req p = p0 /\ q = q0 /\ isSorted(A1) /\ isSorted(A2)
    ens returns(r) /\ (seq2mset(?A) = (seq2mset(A1) U seq2mset(A2))) /\ isSorted(?A) /\ ((r = p0) \/ (r = q0))
    */
{
	struct listNode* t;
	if (q==0) t = p;
	else
	{
    q->next = q->next;
		if (p==0) t = q;
		else
		{
      p->next = p->next;
			if (q->val <p->val)
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


struct listNode* mergesort(struct listNode* p)
/*@ cfg <heap> list(p0)(A) => list(r)(?A) </heap>
    req p = p0
    ens returns(r) /\ (seq2mset(A) = seq2mset(?A)) /\ isSorted(?A)*/
{
	struct listNode* r;
	struct listNode* q;
	q = 0;
	if ((p==0) || (p->next == 0)) r = p;
	else
	{
    p->next = p->next;
		q = split(p);
		q = mergesort(q);
		p = mergesort(p);
		r = merge(p,q);
	}
	return r;
}


void print(struct listNode* x)
{
	while(x!=0)
	{
		printf("%d ",x->val);
		x = x->next;
	}
	printf("\n");
}


int main()
{
	struct listNode *x;
  struct listNode *y;
  x = (struct listNode*)malloc(sizeof(struct listNode));
  x->val = 70;
  x->next = 0;
  y = (struct listNode*)malloc(sizeof(struct listNode));
  y->val = 6;
  y->next = x;
  x = y;
  y = (struct listNode*)malloc(sizeof(struct listNode));
  y->val = 47;
  y->next = x;
  x = y;
  y = (struct listNode*)malloc(sizeof(struct listNode));
  y->val = 52;
  y->next = x;
  x = y;
  y = (struct listNode*)malloc(sizeof(struct listNode));
  y->val = 5;
  y->next = x;
  x = y;
  y = (struct listNode*)malloc(sizeof(struct listNode));
  y->val = 1;
  y->next = x;
  x = y;
  y = (struct listNode*)malloc(sizeof(struct listNode));
  y->val = 111;
  y->next = x;
  x = y;
 
	//print(x);
	y = split(x);
	//print(x);
	//print(y);
	x = merge(x,y);
	x = mergesort(x);
	print(x);
  //@assert <out> 1 @ 5 @ 6 @ 47 @ 52 @ 70 @ 111 </out>
	return 0;
}

//@ var A : Seq

