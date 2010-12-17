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


struct nodeQueue* dequeue(struct nodeQueue *x)
/*@ pre   < config > 
          < env > x |-> x0 </ env > 
          < heap > queue(x0)([val0] @ A)  
              H 
          </ heap >
          < form > ~(x0 === 0) </ form > C </ config > */
/*@ post  < config > 
          < env > ?rho </ env > 
          < heap > queue(x0)(A) H </ heap >
          < form > returns x0 </ form > C </ config > */
{
  struct nodeList* n;
  n = x->head;
  x->head = n->next;
  
  free(n);
  return x;
}

int main()
{
  struct nodeList* x;
  struct nodeList* y;
  struct nodeQueue* q;
  x=(struct nodeList*)malloc(sizeof(struct nodeList));
  y=(struct nodeList*)malloc(sizeof(struct nodeList));
  x->val = 34;
  x->next = 0;
  y->val = 23;
  y->next = x;
  q=(struct nodeQueue*)malloc(sizeof(struct nodeQueue));
  q->head = y;
  q->tail = x;
  // printf("%d %d\n",q->head->val, q->tail->val);
  printf("%d %d\n",q->head, q->tail);
  q = dequeue(q);
  printf("%d %d\n",q->head, q->tail);
  return 0;
}

/*@ var x0 val0 : FreeInt */
/*@ var ?n ?x ?l : ?Int */
/*@ var A : FreeSeq */
/*@ var ?rho : ?MapItem */
/*@ var H : FreeMapItem */
/*@ var !H : !MapItem */
/*@ var C : FreeBagItem */


