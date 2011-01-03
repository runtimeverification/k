#include <stdlib.h>


struct nodeList {
  int val;
  struct nodeList *next;
};

int search(struct nodeList* x, int value)
{
  struct nodeList* iterx;
  int f;
  f = 0;
  iterx = x;
  x->val = x->val;
  while(iterx != 0)
  {
    if (iterx->val == value) f = 1;
    iterx = iterx->next;
  }
  return f;
}

int main()
{
  struct nodeList *x;
  struct nodeList *y;
  int l;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 5;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 7;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 45;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 5;
  y->next = x;
  x = y;
  l = search(x,5);
  return 0;
}

