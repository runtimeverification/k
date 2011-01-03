#include <stdlib.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

int length(struct nodeList* a)
{
  int l;
  struct nodeList* x;
  x = a;
  l = 0;
  
  while (x != 0) {
        x = x->next ;
        l = l + 1 ;
    }
  return l;
}

int main()
{
  int l;
  struct nodeList* x;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 5;
  x->next = 0;
  l = length(x);
  printf("%d ", l);
  printf("\n");
  return 0;
}

