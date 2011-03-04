#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* append(struct listNode *x, struct listNode *y)
//@ pre  <heap> list(x)(A), list(y)(B), H </heap>
//@ post <heap> list(?x)(A @ B), H </heap> /\ returns(?x)
{
  struct listNode *p;
  if (x == 0)
   return y;

  p = x;
  /*@ invariant <heap> lseg(x, p)(?A1), list(p)(?A2), !H </heap> 
                /\ A = ?A1 @ ?A2 /\ ~(p = 0) /\ y = !y */
  while (p->next)
    p = p->next;
  p->next = y;

  return x;
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
//@ pre  <heap> list(x)(?A), H </heap>
//@ post <heap> H </heap>
{
  struct listNode *y;

  //@ invariant <heap> list(x)(?A), H </heap>
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct listNode* x)
//@ pre  <heap>  list(x)(A), H </heap><out> B </out> /\ x = x0
//@ post <heap> list(x0)(A), H </heap><out> B @ A </out>
{
  /*@ invariant <heap> lseg(x0,x)(?A1), list(x)(?A2), H </heap>
                <out> B @ ?A1 </out> /\ A = ?A1 @ ?A2 */
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

  x = create(4);
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

