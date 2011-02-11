#include <stdlib.h>


struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList *copy(struct nodeList *x)
{
  struct nodeList* y;
  struct nodeList* iterx;
  struct nodeList* itery;
  struct nodeList* newnode;

  if (x == 0)
    return 0;

  y = (struct nodeList *)malloc(sizeof(struct nodeList));
  y->val = x->val;
  y->next = 0;
  iterx = x->next;
  itery = y;
  while(iterx) {
    newnode = (struct nodeList *)malloc(sizeof(struct nodeList));
    newnode->val = iterx->val;
    newnode->next = 0;
    itery->next = newnode;
    iterx = iterx->next;
    itery = newnode;
  }

  return y;
}

