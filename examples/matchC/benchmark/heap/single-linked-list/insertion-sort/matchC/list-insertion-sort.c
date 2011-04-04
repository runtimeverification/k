#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* insertionSort(struct listNode* l)
/*@ cfg <heap_> list(l)(L) => list(l)(?L) <_/heap>
    req l = l0
    ens returns(l) /\ (seq2mset(L) = seq2mset(?L)) /\ isSorted(?L) */
{
  struct listNode* x;
  struct listNode* e;
  struct listNode* y;
  x = l;
  l = 0;
/*@ inv <heap_> list(l)(?L), list (x)(?X) <_/heap> /\ (seq2mset(L) = seq2mset(?L) U seq2mset(?X)) /\  isSorted(?L) */
  while(x != 0)
  {
    e = x;
    x = x->next;
    if (l != 0)
    {
      if(e->val> l->val)
      {
        y = l;
/* inv <heap_> lseg(l,y)(?A), lseg(y,?n)([?u]), list(?n)(?B), lseg(e,x)([?v]), list(x)(?X) <_/heap> /\ (seq2mset(L) = seq2mset(?L) U seq2mset([?v] @ ?X)) /\ isSorted(?L) /\ (?L = (?A @ [?u] @ ?B)) /\ @(max(seq2mset(?A) U ({|?u|})) < (?v))*/
        while ((y->next != 0) && (e->val> y->next->val))
        {
          y = y->next;
        }
        e->next = y->next;
        y->next = e;
      }
      else
      {
        e->next = l;
        l = e ;
      }
    }
    else
    {
      e->next = 0;
      l = e ;
    }
  }
  return l;
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

int main()
{
  struct listNode *x;
  struct listNode *y;
  x = create(5);
  x->val = 10;
  print(x);
  x = insertionSort(x);
  print(x);
  return 0;
}

//@ var u, v, n : Int
//@ var A, B, C, L, X : Seq
