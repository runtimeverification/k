#include <stdlib.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* insert(struct nodeList* x, int i)
{
struct nodeList* iNode;
	iNode = (struct nodeList*) malloc (sizeof(struct nodeList));
	iNode->val = i;
	iNode->next = 0;
	if (x == 0) x = iNode;
	else
	{
		if (x->val > i)
		{
			iNode->next = x;
			x = iNode;
		}
		else
		{
			struct nodeList* placement;
			struct nodeList* iterator;
			placement = x->next;
      iterator = placement->next;
      
			while (iterator!=0)
			{
				if(iterator->val > i)
				{
					iterator = iterator->next;
				}
				else
				{
					placement = iterator;
					iterator = iterator->next;
				}
			}
			iNode->next = placement->next;
			placement->next = iNode;
		}
	}
	return x;
}


int main()
{
  struct nodeList *x;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 5;
  x->next = 0;

  x = insert(x,8) ;
  x = insert(x,3) ;
  return 0;
}


