#include <stdlib.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

int length(struct nodeList* a)
{
  int l;
  struct nodeList* x;
  l = 0;
  if(a != 0)
  {
    x = a->next;
    l = length(x) + 1 ;
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
  return 0;
}


