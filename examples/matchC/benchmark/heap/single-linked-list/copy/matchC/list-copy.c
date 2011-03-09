#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode *copy(struct listNode *x)
// pre  <heap> list(x)(A), H </heap> /\ x = x0
// post <heap> list(x0)(A), list(y)(A), H </heap> /\ returns(y)
{
  struct listNode* y;
  struct listNode* ix;
  struct listNode* iy;
  struct listNode* newnode;

  if (x == 0)
    return 0;

  y = (struct listNode *)malloc(sizeof(struct listNode));
  y->val = x->val;
  y->next = 0;
  ix = x->next;
  iy = y;
// invariant <heap> lseg(x0,ix)(?A @ [?v]), list(ix)(?B), lseg(y,iy)(?A), iy |-> ?v : (id("listNode").id("val")), iy +Int 1 |-> 0 : (id("listNode").id("next")), H </heap> /\ A = (?A @ [?v] @ ?B)
  while(ix) {
    newnode = (struct listNode *)malloc(sizeof(struct listNode));
    newnode->val = ix->val;
    newnode->next = 0;
    iy->next = newnode;
    ix = ix->next;
    iy = newnode;
  }

  return y;
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

  x = create(5);
  print(x);
  y = copy(x);
  print(y);
  destroy(x);
  destroy(y);
  return 0;
}


//@ var n : Int
//@ var A, B, C : Seq
//@ var H : MapItem
