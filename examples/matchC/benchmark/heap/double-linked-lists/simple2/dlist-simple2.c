#include <stdlib.h>

struct nodeDList {
  int val;
  struct nodeDList *next;
  struct nodeDList * prev;
};

int length(struct nodeDList* a)
{
  int l;
  struct nodeDList* x;
  x = a->next;
  l = 1;
  
  return l;
}

