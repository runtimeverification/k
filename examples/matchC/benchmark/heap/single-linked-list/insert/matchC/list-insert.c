#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* insert(struct listNode* x, int i)
/* cfg  <heap_> list(x)(A) => list(x)(?A) <_/heap> 
    req i = i0 /\ x = x0
    ens returns(x) /\ (seq2mset(?A) = seq2mset(A @ [i0])) */
{
  
  struct listNode* placement;
  struct listNode* iterator;
  struct listNode* iNode;

	if (x == 0)
  {
  	iNode = (struct listNode*) malloc (sizeof(struct listNode));
    iNode->val = i;
    iNode->next = 0;
    x = iNode;
  }
	else
	{
    if (x->val > i)
		{
      iNode = (struct listNode*) malloc (sizeof(struct listNode));
      iNode->val = i;
			iNode->next = x;
			x = iNode;
		}
		else
		{
      iterator = x->next;
      placement = iterator;
    
// inv <heap_> lseg(x,placement)(?B), lseg(placement,iterator)(?D), list(iterator)(?C) <_/heap> /\ A = (?B @ ?D @ ?C)
      while (iterator)
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
      if (placement == 0)
      {
        iNode = (struct listNode*) malloc (sizeof(struct listNode));
        iNode->val = i;
        iNode->next = 0;
        x->next = iNode;
      }
      else
      {
        iNode = (struct listNode*) malloc (sizeof(struct listNode));
        iNode->val = i;
        iNode->next = placement->next;
        placement->next = iNode;
      }
		}
	}
	return x;
}

void print(struct listNode* x)
/*@ cfg <heap_> list(x0)(A) <_/heap> <out_> epsilon => A </out>
    req x = x0 */
{
  /*@ inv <heap_> lseg(x0,x)(?A1), list(x)(?A2) <_/heap> <out_> ?A1 </out>
          /\ A = ?A1 @ ?A2 */
  while(x)
  {
    printf("%d ",x->val);
    x = x->next;
  }
  printf("\n"); 
}

int main()
{
  struct listNode *x;
  x = (struct listNode*)malloc(sizeof(struct listNode));
  x->val = 5;
  x->next = 0;
  print(x);
  //@ assert <heap_> list(x)([5]) <_/heap>
  // odd behaviour, tool proves the function but cannot assert its precondition
  x = insert(x,8) ;
  x = insert(x,3) ;
  x = insert(x,6) ;
  print(x);
  //@ assert <heap_> list(x)([3, 5, 6, 8]) <_/heap>
  return 0;
}

//@ var i, v1, v2 : Int
//@ var A, B, C, D : Seq
