struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* filter(struct nodeList* x, int i)
{
	struct nodeList* y;
	struct nodeList* z;
	y = x;
  
	while ((y->val == i) && (y != 0))
	{
		x = y->next;
		free(y);
		y = x;
	}
	z = y;
	y = y->next;
  
  
	while(y != 0)
	{
		if(y->val == i)
		{
			z->next = y->next;
			free(y);
			y = z->next;
		}
		else
		{
			z = y;
			y = y ->next;
		}
	}
	return x;
}


