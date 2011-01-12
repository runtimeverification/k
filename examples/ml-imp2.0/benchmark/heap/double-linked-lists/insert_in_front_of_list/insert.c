#include <stdlib.h>
#include <stdio.h>

struct nodeDList {
  int val;
  struct nodeDList *next;
  struct nodeDList * prev;
};

struct nodeDList* insert(struct nodeDList* a, int val)
{
  struct nodeDList* aux;
  aux = (struct nodeDList*)malloc(sizeof(struct nodeDList));
  aux->prev = 0;
  aux->val = val;
  aux->next = a;
  return aux;
}

void print(struct nodeDList* a)
{
  struct nodeDList* aux;
  aux = a;
  printf("\n");
  while(aux!=0)
  {
    printf("%d ", aux->val);
    aux = aux->next;
  }
  printf("\n");
}

int main()
{
  struct nodeDList* x;
  x = (struct nodeDList*)malloc(sizeof(struct nodeDList));
  x->val = 5;
  x->next = 0;
  x->prev = 0;
  print(x);
  x = insert(x,7);
  x = insert(x,10);
  x = insert(x,8);
  print(x);
  return 0;
}


/*@ var ?x ?l ?y ?z : ?Int */
/*@ var a0 b0 : FreeInt */
/*@ var ?A ?X : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var H : FreeMapItem */
