#include <stdlib.h>

struct nodeDList {
  int val;
  struct nodeDList *next;
  struct nodeDList * prev;
};

/*@ verify */
int main()
{
  struct nodeDList* x;
  x = (struct nodeDList*)malloc(sizeof(struct nodeDList));
  x->val = 5;
  x->next = 0;
  x->prev = 0;
  return 0;
}

