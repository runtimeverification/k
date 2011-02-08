#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* reverse(struct listNode *x)
{
  struct listNode *p;
  struct listNode *y;
  p = 0 ;
  while(x) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}

struct listNode* append(struct listNode *x, struct listNode *y)  
{
  struct listNode *p;
  if (x == 0)
   return y;

  p = x;
  while (p->next)
    p = p->next;
  p->next = y ;

  return x;
}

int length(struct listNode* x)
{
  int l;
  
  l = 0;
  while (x) {
    l += 1;
    x = x->next ;
  }

  return l;
}


struct listNode* create(int n)
{
  struct listNode *x;
  struct listNode *y;
  x = 0;
  while (n)
  {
    y = x;
    x = (struct listNode*)malloc(sizeof(struct listNode));
    x->val = n;
    x->next = y;
    n -= 1;
  }
  return x;
}

void destroy(struct listNode* x)
{
  struct listNode *y;
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct listNode* x)
{
  while(x)
  {
    printf("%d ",x->val);
    x = x->next;
  }
  printf("\n"); 
}


int main()
{
  struct listNode *x;
  struct listNode *y;

  x = create(5);
  printf("x: ");
  print(x);
  x = reverse(x);
  printf("reverse(x): ");
  print(x);
  destroy(x);

  x = create(3);
  printf("x: ");
  print(x);
  y = create(3);
  printf("y: "); 
  print(y);
  x = append(x, y);
  printf("append(x, y): ");
  print(x);
  destroy(x);

  return 0;
}

