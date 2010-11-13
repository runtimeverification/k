#include <stdlib.h>
#include <stdio.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* reverse(struct nodeList *x)
{
  struct nodeList *p;
  struct nodeList *y;
  p = 0 ;
  while(x) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}


struct nodeList* append(struct nodeList *x, struct nodeList *y)  
{
  struct nodeList *p;
  if (x == 0)
   return y;

  p = x;
  while (p->next)
    p = p->next;
  p->next = y ;

  return x;
}


int length(struct nodeList* x)
{
  int l;
  
  l = 0;
  while (x) {
    l += 1;
    x = x->next ;
  }

  return l;
}


struct nodeList* create(int n)
{
  struct nodeList *x;
  struct nodeList *y;
  x = 0;
  while (n)
  {
    y = x;
    x = (struct nodeList*)malloc(sizeof(struct nodeList));
    x->val = n;
    x->next = y;
    n -= 1;
  }
  return x;
}


void destroy(struct nodeList* x)
{
  struct nodeList *y;
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct nodeList* x)
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
  struct nodeList *x;
  struct nodeList *y;
//  x = create(5);
//  x = reverse(x);
//  destroy(x);
  x = create(5);
  printf("x: ");
  print(x);
  x = reverse(x);
  printf("reverse(x): ");
  print(x);
  destroy(x);

//  x = create(3);
//  y = create(3);
//  x = append(x, y);
//  destroy(x);
  x = create(3);
  printf("x: ");
  print(x);
  y = create(3);
  printf("y: "); 
  print(x);
  x = append(x, y);
  printf("append(x, y): ");
  print(x);
  destroy(x);
  return 0;
}


/*@ var ?x ?y ?p ?i ?v : ?Int */
/*@ var x0 : FreeInt */
/*@ var ?B ?C ?A1 ?A2 : ?Seq */
/*@ var !A !A1 !A2 : !Seq */
/*@ var A B : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var !rho !H : !MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */
