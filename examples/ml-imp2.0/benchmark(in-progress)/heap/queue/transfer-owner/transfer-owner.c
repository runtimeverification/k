#include <stdlib.h>
#include <stdio.h>

struct nodeList {
int val;
struct nodeList *next;
};

struct nodeQueue {
struct nodeList* head;
struct nodeList* tail;
};


struct nodeQueue* transfer(struct nodeQueue *dest, struct nodeQueue* src)
/*@ pre   < config > 
          < env > dest |-> dest0 src |-> src0 </ env > 
          < heap > queue(dest0)(A) queue(src0)(B) H </ heap >
          < form > TrueFormula </ form > C </ config > */
/*@ post  < config > 
          < env > ?rho </ env > 
          < heap > queue(dest0)(A @ [?v]) queue(src0)(?B) H </ heap >
          < form > returns dest0 /\ (B === [?v] @ B) </ form > C </ config >
          < config >
          < env > ?rho </ env >
          < heap > queue(dest0)(A) queue(src0)(B) H </ heap >
          < form > returns dest0 /\ (dest0 === 0) \/ (src0 === 0) \/ (B === epsilon) </ form > C
          </ config >
          */
{
  struct nodeList* n;
  
  if (src != 0)
  {
    if (dest != 0)
    {
      if(src->head != 0)
      {
        n = src->head;
        if(src->head == src->tail)
        {
          src->head = 0;
          src->tail = 0;
        }
        else
        {
          src->head = n->next;
        }
        if(dest->head !=0)
        {
          dest->tail->next = n;
        }
        else
        {
          dest->head = n;
        }
        dest->tail = n;
      }
    }
  }
  return dest;
}

int main()
{
  struct nodeQueue* x;
  struct nodeQueue* y;
  struct nodeList *f;
  struct nodeList* l;

  f = (struct nodeList*)malloc(sizeof(struct nodeList));
  l = (struct nodeList*)malloc(sizeof(struct nodeList));
  x = (struct nodeQueue*)malloc(sizeof(struct nodeQueue));
  y = (struct nodeQueue*)malloc(sizeof(struct nodeQueue));
  l->val=6;
  l->next=0;
  f->val = 5;
  f->next = l;
  x->head=f;
  x->tail=l;
  y->head=f;
  y->tail=l;
  printf("%d %d\n",x->head->val, x->tail->val);
  x = transfer(x,y);
  printf("%d %d %d\n",x->head->val, x->head->next->val,x->tail->val);
  return 0;
}

/*@ var x0 val0 dest0 src0 : FreeInt */
/*@ var ?n ?x ?u ?v : ?Int */
/*@ var A B : FreeSeq */
/*@ var ?B : ?Seq */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var !H : !MapItem */
/*@ var C : FreeBagItem */
