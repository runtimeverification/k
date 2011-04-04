#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* prefix(struct listNode* x, int i)
/*@ cfg  <heap> list(x)(A) => list(x)([i0] @ A) </heap>
    req i = i0 
    ens returns(x)*/
{
	struct listNode* y;
	y = (struct listNode*) malloc (sizeof(struct listNode));
	y->val = i;
	y->next = x;
  x = y;
	return x;
}

int main()
{
  struct listNode *x;
  x = (struct listNode*)malloc(sizeof(struct listNode));
  x->val = 6;
  x->next = 0;
  //@ assert <heap> list(x)([6]) </heap>
  x = prefix(x,5) ;
  //@ assert <heap> list(x)([5, 6]) </heap>
  return 0;
}


//@ var A : Seq

