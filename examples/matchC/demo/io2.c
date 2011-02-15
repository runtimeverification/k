#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


void readWrite()
{
  int t;
  int n;

  scanf("%d", &n);

  while (n) {
    scanf("%d", &t);
    printf("%d ", t);
    n -= 1;
  }
}


void readWriteBuffer()
{
  int i;
  int n;
  struct listNode *x;
  struct listNode *y;

  scanf("%d", &n);

  i = 0;
  x = 0;
  while (i < n) {
    y = x;
    x = (struct listNode*) malloc(sizeof(struct listNode));
    scanf("%d", &(x->val));
    x->next = y;
    i += 1;
  }

  i = 0;
  while (i < n) {
    y = x->next;
    printf("%d ",x->val);
    free(x);
    x = y;
    i += 1;
  }
}


int main()
{
  /*@ assume <in> [5, 1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10] </in>
             <out> epsilon </out> */
  readWrite();
  //@ assert <in> [5, 6, 7, 8, 9, 10] </in><out> [1, 2, 3, 4, 5] </out>

  readWriteBuffer();
  //@ assert <in> epsilon </in><out> [1, 2, 3, 4, 5, 10, 9, 8, 7, 6] </out>

  return 0;
}

