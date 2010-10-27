#include <stdlib.h>

struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* copy(struct nodeList *x)
/*@ pre < config > < env > x |-> x0 </ env > < heap > list(x0)(A) </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(x0)(A) list(?y)(A) </ heap > < form > returns ?y </ form > </ config > */
{
	struct nodeList* y;
	struct nodeList* iterx;
	struct nodeList* itery;
  if (x == 0) { y = 0;}
  else
  {
	y = (struct nodeList*)malloc(sizeof(struct nodeList));
	y->val = x->val;
	y->next = 0;
	iterx = x->next;
	itery = y;

/*@ assert < config > 
          < env > iterx |-> ?ix itery |-> ?iy x |-> x0 y |-> ?y </ env >
          < heap > 
                   x0  |-> ?v : (nodeList . val)
                   (x0 +Int 1) |-> ?ix : (nodeList . next)
                   list(?ix)(?A) 
                   list(?y)(?B) </ heap >
          < form > A === ([?v] @ ?A) /\ ([?v] === ?B) </ form > 
          </ config > */
          
/*@ assert < config > 
          < env > iterx |-> ?ix itery |-> ?iy x |-> x0 y |-> ?y </ env >
          < heap > 
                   lseg(x0,?ix)(?A)
                   list(?ix)(?B) 
                   list(?y)(?C) </ heap >
          < form > A === (?A @ ?B) /\ (?A === ?C) </ form > 
          </ config > */
    
/*@ invariant < config > 
              < env > iterx |-> ?ix itery |-> ?iy x |-> x0 y |-> ?y </ env >
              < heap > lseg(x0,?ix)(?A) list(?ix)(?B) list(?y)(?C) </ heap >
              < form > A === (?A @ ?B) /\ (?A === ?C) </ form > 
              </ config > */
    while(iterx != 0) {
      struct nodeList* newnode;
      newnode =  (struct nodeList*)malloc(sizeof(struct nodeList));
      newnode->val = iterx->val;
      newnode->next = 0;
      itery->next = newnode;
      itery = newnode;
      iterx = iterx->next;
    }
  }
  return y;
}



int main()
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > ?H </ heap > < form > TrueFormula </ form > </ config > */
{
  struct nodeList *x;
  x = (struct nodeList*)malloc(sizeof(struct nodeList));
  free(x);
  return 0;
}


/*@ var ?y ?ix ?iy ?nn ?v : ?Int */
/*@ var x0 : FreeInt */
/*@ var ?A ?B ?C : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
