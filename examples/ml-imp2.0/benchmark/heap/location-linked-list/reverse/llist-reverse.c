#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* reverse(struct nodeList *x)
{
  struct nodeList *p;
  struct nodeList *y;
  p = 0 ;
  while(x != 0) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}


int main()
{
  struct nodeList *x;
  struct nodeList *y;
    
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
  printf("x: %d %d %d\n",x, x->next, x->next->next);
  x = reverse(x) ;
  printf("x: %d %d %d\n",x, x->next, x->next->next);
  return 0;
}

