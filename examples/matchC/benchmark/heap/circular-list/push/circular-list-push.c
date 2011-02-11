#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

struct nodeList* clpush(struct nodeList* x, int val)
{
  struct nodeList* aux;
  aux = (struct nodeList*)malloc(sizeof(struct nodeList));
  aux->val = val;
  aux->next = x->next;
  x->next = aux;
  return x;
}


int main()
{
  struct nodeList *x;
  struct nodeList *y;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 5;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 8;
  y->next = x;
  x->next = y;
  printf("%d %d\n", x->val, y->val);
  x = clpush(x,9);
  printf("%d %d %d\n", x->val, x->next->val, x->next->next->val);
  return 0;
}

