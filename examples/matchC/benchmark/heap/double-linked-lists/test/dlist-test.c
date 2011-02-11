#include <stdlib.h>
#include <stdio.h>

struct nodeDList {
  int val;
  struct nodeDList *next;
  struct nodeDList * prev;
};

int length(struct nodeDList* a)
{
  int l;
  struct nodeDList* x;
  l = 0;
  if (a != 0)
  {             
  x = a;
	while (x != 0) {
		  x = x->next ;
		  l = l + 1 ;
	  }
  }
  return l;
}

int main()
{
  struct nodeDList* x;
  x = (struct nodeDList*)malloc(sizeof(struct nodeDList));
  x->val = 5;
  x->next = 0;
  x->prev = 0;
  printf("%d\n", length(x));
  return 0;
}


