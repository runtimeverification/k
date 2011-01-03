#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* append(struct nodeList *x, struct nodeList *y)  
{
  struct nodeList *p;
  struct nodeList *i;
  if (x == 0) x = y;
  else
  {
    p = x ;
    i = x->next; 
    while (i != 0)
    {
        p = i ;
        i = i->next;
    }
    p->next = y ;
  }
  return x;
}

int main()
{
  struct nodeList *x;
  struct nodeList *y;
  struct nodeList *z;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 7;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 6;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 5;
  y->next = x;
  x = y;
  
  printf("x: %d %d %d\n",x->val, x->next->val, x->next->next->val);
  z = (struct nodeList*)malloc(sizeof(struct nodeList));
  z->val = 5;
  z->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 3;
  y->next = z;
  z = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 1;
  y->next = z;
  z = y;
  printf("z: %d %d %d\n",z->val, z->next->val, z->next->next->val);
  
  x = append(x,z);
  printf("x: %d %d %d %d %d %d\n",x->val, x->next->val, x->next->next->val, x->next->next->next->val, x->next->next->next->next->val, x->next->next->next->next->next->val);
  
  y = x;
  x = x->next;
  free(y);
  y = x;
  x = x->next;
  free(y);
  y = x;
  x = x->next;
  free(y);
  y = x;
  x = x->next;
  free(y);
  y = x;
  x = x->next;
  free(y);
  y = x;
  x = x->next;
  free(y);
  
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 7;
  x->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 6;
  y->next = x;
  x = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 5;
  y->next = x;
  x = y;
  
  z = (struct nodeList*)malloc(sizeof(struct nodeList));
  z->val = 5;
  z->next = 0;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 3;
  y->next = z;
  z = y;
  y = (struct nodeList*)malloc(sizeof(struct nodeList));
  y->val = 1;
  y->next = z;
  z = y;
  
  x = append(x,z);
  
  return 0;
}

