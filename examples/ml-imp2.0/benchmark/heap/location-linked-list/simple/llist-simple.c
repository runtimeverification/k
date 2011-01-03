#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

int main()
{
  struct nodeList *x;
  struct nodeList *y;
  struct nodeList *p;
  p = 0 ;
    
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 7;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 6;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 5;
  y->next = x;
  x = y;
  printf("x: %d %d %d\n",x->val, x->next->val, x->next->next->val);
  while(x != 0) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return 0;
}

