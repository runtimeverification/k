#include <stdlib.h>

struct nodeList {
  int val;
  struct nodeList *next;
};

struct nodeList* prefix(struct nodeList* x, int i)
{
	struct nodeList* y;
	y = (struct nodeList*) malloc (sizeof(struct nodeList));
	y->val = i;
	y->next = x;
	return y;
}

int main()
{
  struct nodeList *x;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 6;
  x->next = 0;
  
  x = prefix(x,5) ;
  return 0;
}


