#include <stdlib.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

struct nodeList* create()
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
  return x;
}

int main()
{
  struct nodeList *x;
  x = create();
  return 0;
}

