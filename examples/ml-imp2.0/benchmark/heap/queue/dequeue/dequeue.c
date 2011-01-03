#include <stdlib.h>
#include <stdio.h>

struct nodeList {
int val;
struct nodeList *next;
};

struct nodeQueue {
struct nodeList* head;
struct nodeList* tail;
};


struct nodeQueue* dequeue(struct nodeQueue *x)
{
  struct nodeList* n;
  /* n = x->head;
  x->head = n->next;
  free(n); */
  
  n = 0;

  if (x->head != 0)
  {
    n = x->head;
    if (x->head == x->tail)
    {
      x->head = n->next;
      x->tail = n->next;
    }
    else x->head = n->next;
  }
  free(n);

  return x;
}

int main()
{
  struct nodeList* x;
  struct nodeList* y;
  struct nodeQueue* q;
  x=(struct nodeList*)malloc(sizeof(struct nodeList));
  y=(struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 34;
  x->next = 0;
  y->val = 23;
  y->next = x;
  q=(struct nodeQueue*)malloc(sizeof(struct nodeQueue));
  q->head = y;
  q->tail = x;
  // printf("%d %d\n",q->head->val, q->tail->val);
  printf("%d %d\n",q->head, q->tail);
  q = dequeue(q);
  printf("%d %d\n",q->head, q->tail);
  return 0;
}

