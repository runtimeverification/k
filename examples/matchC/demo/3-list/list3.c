#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* reverse(struct listNode *x)
/*@ rule <k> $ => return p1; </k>
         <heap_> list(x)(A) => list(p1)(rev(A)) <_/heap> */
{
  struct listNode *p;

  p = 0 ;
  //@ inv <heap_> list(p)(?B), list(x)(?C) <_/heap> /\ A = rev(?B) @ ?C
  while(x) {
    struct listNode *y;

    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }

  return p;
}

struct listNode* append(struct listNode *x, struct listNode *y)
/*@ rule <k> $ => return x1; </k>
         <heap_> list(x)(A), list(y)(B) => list(x1)(A @ B) <_/heap> */
{
  struct listNode *p;
  if (x == 0)
    return y;

  p = x;
  /*@ inv <heap_> lseg(x, p)(?A1), list(p)(?A2) <_/heap> 
          /\ A = ?A1 @ ?A2 /\ ~(p = 0) /\ y = !y */
  while (p->next)
    p = p->next;
  p->next = y;

  return x;
}

int length(struct listNode* x)
//@ rule <k> $ => return len(A); </k> <heap_> list(x)(A) <_/heap>
{
  int l;
  
  l = 0;
  /*@ inv <heap_> lseg(old(x), x)(?A1), list(x)(?A2) <_/heap> 
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
//@ rule <k> $ => return; </k><heap_> list(x)(A) => . <_/heap>
{
  //@ inv <heap_> list(x)(?A) <_/heap>
  while(x)
  {
    struct listNode *y;

    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct listNode* x)
/*@ rule <k> $ => return; </k>
         <heap_> list(x)(A) <_/heap>
         <out_> epsilon => A </out> */
{
  /*@ inv <heap_> lseg(old(x), x)(?A1), list(x)(?A2) <_/heap> <out_> ?A1 </out>
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
  //@ assert <heap> list(x)(A1) </heap>
  x = reverse(x);
  printf("reverse(x): ");
  print(x);
  //@ assert <heap> list(x)(rev(A1)) </heap>
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
  //@ assert <heap> list(x)(A2) </heap>
  y = create(3);
  printf("y: ");
  print(y);
  //@ assert <heap> list(x)(A2), list(y)(A3) </heap>
  x = append(x, y);
  printf("append(x, y): ");
  print(x);
  //@ assert <heap> list(x)(A2 @ A3) </heap>
  destroy(x);
  //@ assert <heap> . </heap>

  return 0;
}


//@ var A, B, C : Seq

