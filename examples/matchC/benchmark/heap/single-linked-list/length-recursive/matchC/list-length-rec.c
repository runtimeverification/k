#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};

int length(struct listNode* x)
/*@ cfg  <heap_> list(x)(A) => list(x0)(A) <_/heap> 
    req x = x0
    ens returns(len(A)) */
{
  if (x == 0) return 0;
  else 
  {
    return (length(x->next) + 1);
  }
}

struct listNode* create(int n)
{
  struct listNode *x;
  struct listNode *y;
  x = 0;
  while (n)
  {
    y = x;
    x = (struct listNode*)malloc(sizeof(struct listNode));
    x->val = n;
    x->next = y;
    n -= 1;
  }
  return x;
}

void destroy(struct listNode* x)
//@ cfg  <heap_> list(x)(?A) => . <_/heap>
{
  struct listNode *y;

  //@ invariant <heap_> list(x)(?A) <_/heap>
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
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
  int n;

  x = create(5);
  //@ assert <heap_> list(x)([1, 2, 3, 4, 5]) <_/heap>
  n = length(x);
  //@ assert <heap_> list(x)([1, 2, 3, 4, 5]) <_/heap>
  destroy(x);
  //@ assert <heap_> . <_/heap>
  return 0;
}


//@ var n : Int
//@ var A, B, C : Seq

