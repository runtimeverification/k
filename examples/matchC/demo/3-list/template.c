#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* reverse(struct listNode *x)
//@ cfg <heap_> list(x)(A) => list(p)(rev(A)) <_/heap> ens returns(p)
{
  struct listNode *p;
  struct listNode *y;

  p = 0 ;
  //@ inv <heap_> list(p)(?B), list(x)(?C) <_/heap> /\ A = rev(?B) @ ?C
  while(x) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }

  return p;
}

struct listNode* append(struct listNode *x, struct listNode *y)
/*@ cfg <heap_> list(x)(A), list(y)(B) => list(?x)(A @ B) <_/heap>
    ens returns(?x) */
{
  struct listNode *p;
  if (x == 0)
   return y;

  p = x;
  /*@ inv <heap_> lseg(x, p)(?A1), list(p)(?A2), !H <_/heap> 
          /\ A = ?A1 @ ?A2 /\ ~(p = 0) /\ y = !y */
  while (p->next)
    p = p->next;
  p->next = y;

  return x;
}

int length(struct listNode* x)
//@ cfg <heap_> list(x0)(A) <_/heap> req x = x0 ens returns(len(A))
{
  int l;
  
  l = 0;
  /*@ inv <heap_> lseg(x0,x)(?A1), list(x)(?A2) <_/heap> 
          /\ A = ?A1 @ ?A2 /\ l = len(?A1) */
  while (x) {
    l += 1;
    x = x->next ;
  }

  return l;
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
//@ cfg <heap_> list(x)(?A) => . <_/heap>
{
  struct listNode *y;

  //@ inv <heap_> list(x)(?A) <_/heap>
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct listNode* x)
//@ cfg <heap_> list(x0)(A) <_/heap> <out_> epsilon => A </out> req x = x0
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
  struct listNode *y;

  x = create(5);
  //@ assert <heap> list(x)([1, 2, 3, 4, 5]) </heap>
  x = reverse(x);
  //@ assert <heap> list(x)([5, 4, 3, 2, 1]) </heap>
  destroy(x);
  //@ assert <heap> . </heap>
  x = create(5);
  printf("x: ");
  print(x);
  //@ assert <heap> list(x)(!A) </heap>
  x = reverse(x);
  printf("reverse(x): ");
  print(x);
  //@ assert <heap> list(x)(rev(!A)) </heap>
  destroy(x);

  x = create(3);
  //@ assert <heap> list(x)([1, 2, 3]) </heap>
  y = create(3);
  //@ assert <heap> list(x)([1, 2, 3]), list(y)([1, 2, 3]) </heap>
  x = append(x, y);
  //@ assert <heap> list(x)([1, 2, 3, 1, 2, 3]) </heap>
  destroy(x);
  //@ assert <heap> . </heap>
  x = create(3);
  printf("x: ");
  print(x);
  //@ assert <heap> list(x)(!A1) </heap>
  y = create(3);
  printf("y: ");
  print(y);
  //@ assert <heap> list(x)(!A1), list(y)(!A2) </heap>
  x = append(x, y);
  printf("append(x, y): ");
  print(x);
  //@ assert <heap> list(x)(!A1 @ !A2) </heap>
  destroy(x);
  //@ assert <heap> . </heap>
  
  return 0;
}


//@ var n : Int
//@ var A, B, C : Seq
//@ var H : MapItem

