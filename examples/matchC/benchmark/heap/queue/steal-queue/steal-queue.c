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


struct nodeQueue* steal(struct nodeQueue *dest, struct nodeQueue* src)
{
  if (src != 0)
  {
    if (dest != 0)
    {
      if (src->head != 0)
      {
        if(dest->head != 0)
        {
          dest->tail->next = src->head;
        }
        else
        {
          dest->head = src->head;
        }
        dest->tail = src->tail;
      }
      free(src);
    }
  }
  return dest;
}

int main()
{
  struct nodeQueue* x;
  struct nodeQueue* y;
  struct nodeList *f;
  struct nodeList* l;

  f = (struct nodeList*)malloc(sizeof(struct nodeList));
  l = (struct nodeList*)malloc(sizeof(struct nodeList));
  x = (struct nodeQueue*)malloc(sizeof(struct nodeQueue));
  y = (struct nodeQueue*)malloc(sizeof(struct nodeQueue));
  l->val=6;
  l->next=0;
  f->val = 5;
  f->next = l;
  x->head=f;
  x->tail=l;
  y->head=f;
  y->tail=l;
  printf("%d %d\n",x->head, x->head->next);
  x = steal(x,y);
  printf("%d %d %d %d\n",x->head, x->head->next,x->head->next->next, x->head->next->next->next);
  return 0;
}

