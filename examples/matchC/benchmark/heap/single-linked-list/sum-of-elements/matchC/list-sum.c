#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};

int summ(struct listNode* a)
//@ pre  <heap> list(a)(A), H </heap> /\ a = a0
//@ post <heap> list(a0)(A), H </heap> /\ returns(thesum(A))
{
  int s;
  struct listNode* x;
  x = a;
  s = 0;
//@ invariant <heap> lseg(a0,x)(?A), list(x)(?X), H </heap> /\ (?A @ ?X) = A /\ (s = thesum(?A))
  while (x != 0) {
    s = s + x->val;
    x = x->next;
  }
  return s;
}

int main()
{
  int s;
  struct listNode* x;
  struct listNode* y;
  x = (struct listNode*)malloc(sizeof(struct listNode));
  x->val = 5;
  x->next = 0;
  y = (struct listNode*)malloc(sizeof(struct listNode));
  y->val = 4;
  y->next = x;
  x = y;
  y = (struct listNode*)malloc(sizeof(struct listNode));
  y->val = 3;
  y->next = x;
  x = y;
  s = summ(x);
  printf("%d\n", s);
  // assert <out> [content] </out>
  return 0;
}

//@ var s : Int
//@ var A, X : Seq
//@ var H : MapItem
