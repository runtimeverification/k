#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

struct nodeList* swap(struct nodeList* x)
{
  struct nodeList* p;
  p = x;
  x = x->next;
  p->next = x->next;
  x->next = p;
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


int main()
{
  struct nodeList *x;
  struct nodeList *y;
  x = create(5);
  
  print(x);
  x->next = x->next;
  x->next->next = x->next->next;
  x = swap(x);
  print(x);
  
  return 0;
}

