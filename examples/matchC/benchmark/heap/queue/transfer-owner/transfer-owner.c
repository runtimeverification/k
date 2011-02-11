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


struct nodeQueue* transfer(struct nodeQueue *dest, struct nodeQueue* src)
{
  struct nodeList* n;
  
  if (src != 0)
  {
    if (dest != 0)
    {
      if(src->head != 0)
      {
        n = src->head;
        if(src->head == src->tail)
        {
          src->head = 0;
          src->tail = 0;
        }
        else
        {
          src->head = n->next;
        }
        if(dest->head !=0)
        {
          dest->tail->next = n;
        }
        else
        {
          dest->head = n;
        }
        dest->tail = n;
      }
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
  printf("%d %d\n",x->head->val, x->tail->val);
  x = transfer(x,y);
  printf("%d %d %d\n",x->head->val, x->head->next->val,x->tail->val);
  return 0;
}

