#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


int main()
{
  struct listNode *x;

  x = (struct listNode*) malloc(sizeof(struct listNode));
  printf("%p\n", x->next);
}

