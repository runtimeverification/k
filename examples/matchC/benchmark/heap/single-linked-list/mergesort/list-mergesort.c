#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};



struct nodeList* split(struct nodeList* p)
{
	struct nodeList* r;
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
//breaker
struct nodeList* merge(struct nodeList* p, struct nodeList* q)
{
	struct nodeList* t;
	if (q==0) t = p;
	else
	{
    q->next = q->next;
		if (p==0) t = q;
		else
		{
      p->next = p->next;
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
{
	struct nodeList* r;
	struct nodeList* q;
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


