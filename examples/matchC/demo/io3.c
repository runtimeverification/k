#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


void readWrite(int n)
//@ pre  <in> A @ In </in> <out> Out </out> /\ len(A) = n
//@ post <in> In </in> <out> Out @ A </out>
{
  int t;

  /*@ invariant <in> ?B @ In </in> <out> Out @ ?A </out>
                /\ n >= 0 /\ len(?B) = n /\ A = ?A @ ?B */
  while (n) {
    scanf("%d", &t);
    printf("%d ", t);
    n -= 1;
  }
}


void readWriteBuffer(int n)
//@ pre  <in> A @ In </in> <out> Out </out> /\ len(A) = n
//@ post <in> In </in> <out> Out @ rev(A) </out>
{
  int i;
  struct listNode *x;
  struct listNode *y;

  i = 0;
  x = 0;
  /*@ invariant <in> ?B @ In </in> <heap> list(x)(?A), !H </heap>
                /\ i <= n /\ len(?B) = n - i /\ A = rev(?A) @ ?B */
  while (i < n) {
    y = x;
    x = (struct listNode*) malloc(sizeof(struct listNode));
    scanf("%d", &(x->val));
    x->next = y;
    i += 1;
  }

  /*@ invariant <out> Out @ ?A </out> <heap> list(x)(?B), !H </heap>
                /\ A = rev(?A @ ?B) */
  while (x) {
    y = x->next;
    printf("%d ",x->val);
    free(x);
    x = y;
  }
}


int main()
{
  int n;
  /*@ assume <in> [5, 1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10] </in>
             <out> epsilon </out> */

  scanf("%d", &n);
  readWrite(n);
  //@ assert <in> [5, 6, 7, 8, 9, 10] </in> <out> [1, 2, 3, 4, 5] </out>

  scanf("%d", &n);
  readWriteBuffer(n);
  //@ assert <in> epsilon </in> <out> [1, 2, 3, 4, 5, 10, 9, 8, 7, 6] </out>

  return 0;
}


//@ var A, B, In, Out : Seq
//@ var H : MapItem

