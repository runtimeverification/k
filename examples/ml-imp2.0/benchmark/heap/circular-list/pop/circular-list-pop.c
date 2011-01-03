#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

struct nodeList* clpop(struct nodeList* x)
{
  struct nodeList* t;
  struct nodeList* aux;
  t = x->next;
  if (x != t)
  {
    x->next = t->next;
    aux = t->next;
    free(t);
  }
  else
  {
    free(t);
  }
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
  x = clpop(x);
  printf("%d\n", x->val);
  return 0;
}

