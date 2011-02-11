#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* insertionSort(struct nodeList* l)
{
  struct nodeList* x;
  struct nodeList* e;
  struct nodeList* y;
  x = l;
  l = 0;
  while(x != 0)
  {
    e = x;
    x = x->next;
    if (l != 0)
    {
      if(e->val > l->val)
      {
        y = l;
        while ((y->next != 0) && (e->val > y->next->val))
        {
          y = y->next;
        }
        e->next = y->next;
        y->next = e;
      }
      else
      {
        e->next = l;
        l = e ;
      }
    }
    else
    {
      e->next = 0;
      l = e ;
    }
  }
  return l;
}

struct nodeList* print(struct nodeList* x)
{
  struct nodeList* smth;
  smth = x;
  while(smth != 0)
  {
    printf("%d ", smth->val);
    smth = smth->next;
  }
  printf("\n");
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

int main()
{
  struct nodeList *x;
  struct nodeList *y;
  x = create(5);
  x->val = 10;
  print(x);
  x = insertionSort(x);
  print(x);
  return 0;
}


