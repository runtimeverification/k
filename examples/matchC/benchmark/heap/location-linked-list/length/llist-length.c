#include <stdlib.h>
#include <stdio.h>

struct nodeLllist {
  struct nodeLllist *next;
};

int length(struct nodeLllist* a)
{
  int l;
  struct nodeLllist* x;
  if (a==0) l = 0;
  {
    a->next = a->next;
    x = a->next;
    l = 1;
    while (x != 0) {
          x = x->next ;
          l = l + 1 ;
      }
  }
  return l;
}

int main()
{
  int l;
  struct nodeLllist* x;
  struct nodeLllist* y;
  x = (struct nodeLllist*)malloc(sizeof(struct nodeLllist));
  x->next = 0;
  y = (struct nodeLllist*)malloc(sizeof(struct nodeLllist));
  y->next = x;
  printf("%d %d %d\n", y,y->next,y->next->next);
  l = length(y);
  printf("%d\n",l);
  return 0;
}

