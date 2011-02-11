#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* bubble(struct nodeList* x)
{
  int change;
  int tmp;
  struct nodeList* p;
  struct nodeList* r;
  if (x != 0)
  {
    change = 1;
    while(change)
    {
      change = 0;
      p = x;
      r = x->next;
      while (r != 0)
      {
        if (p->val > r->val)
        {
          change = 1;
          tmp = p->val;
          p->val = r->val;
          r->val = tmp;
          /* assert (.).Bag */
        }
        p = r;
        r = r->next;
      }
    }
  }
  return x;
}


struct nodeList* create(int n)
{
  struct nodeList *x;
  struct nodeList *y;
  x = 0;
  while (n)
  {
    y = x;
    x = (struct nodeList*)malloc(sizeof(struct nodeList));
    x->val = n;
    x->next = y;
    n -= 1;
  }
  return x;
}


void destroy(struct nodeList* x)
{
  struct nodeList *y;
  while(x != 0)
  {
    y = x->next;
    free(x);
    x = y;
  }
}



int main()
{
  struct nodeList *x;
  x = create(5);
  x = bubble(x);
  destroy(x);
  return 0;
}


