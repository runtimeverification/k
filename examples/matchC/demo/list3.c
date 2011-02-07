#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* reverse(struct listNode *x)
//@ pre  <heap> list(x)(A), H </heap>
//@ post <heap> list(p)(rev(A)), H </heap> /\ returns(p)
{
  struct listNode *p;
  struct listNode *y;

  p = 0 ;
  /*@ invariant <heap> list(p)(?B), list(x)(?C), H </heap>
                /\ rev(A) = rev(?C) @ ?B */
  while(x) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }

  return p;
}

struct listNode* append(struct listNode *x, struct listNode *y)  
//@ pre  <heap> list(x)(A), list(y)(B), H </heap> /\ y = y0
//@ post <heap> list(?x)(A @ B), H </heap> /\ returns(?x)
{
  struct listNode *p;
  if (x == 0)
   return y;

  p = x;
  /*@ invariant <heap> lseg(x, p)(?A1), list(p)(?A2), !H </heap> 
                /\ A = ?A1 @ ?A2 /\ ~(p = 0) /\ y = y0 */
  // need way to specify y is constant 
  while (p->next)
    p = p->next;
  p->next = y;

  return x;
}

int length(struct listNode* x)
//@ pre  <heap> list(x0)(A), H </heap> /\ x = x0
//@ post <heap> list(x0)(A), H </heap> /\ returns(len(A))
{
  int l;
  
  l = 0;
  /*@ invariant <heap> lseg(x0,x)(?A1), list(x)(?A2), H </heap>
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
{
  struct listNode *y;
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct listNode* x)
{
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
  print(x);
  //@ assert <heap> list(x)(!A1), list(y)(!A2) </heap> 
  x = append(x, y);
  printf("append(x, y): ");
  print(x);
  //@ assert <heap> list(x)(!A1 @ !A2) </heap> 
  destroy(x);
  //@ assert <heap> . </heap> 
  
  return 0;
}


//@ var n, v : Int
//@ var A, B, C : Seq
//@ var H : FreeMapItem
//@ var !H : !MapItem

