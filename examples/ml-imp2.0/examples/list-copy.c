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
              < env > iterx |-> ?ix itery |-> ?y x |-> x0 y |-> ?y </ env >
              < heap > lseg(x0,?ix)(?A) list(?ix)(?B) lseg(?y,0)(?C)
              </ heap >
              < form > A === (?A @ ?B) /\ (?A === ?C) </ form > 
              </ config > */
    
/*@ invariant < config > 
              < env > iterx |-> ?ix itery |-> ?iy x |-> x0 y |-> ?y </ env >
              < heap > lseg(x0,?ix)(?A) list(?ix)(?B) lseg(?y,?iy)(?C)
              </ heap >
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

/*@ assert < config > < env > iterx |-> ?ix itery |-> ?iy x |-> x0 y |-> ?y </ env > 
           < heap > list(x0)(A) 
                    lseg(?y,?iy)(?A)
                    ?iy |-> ?vit : (nodeList . val)
                    (?iy +Int 1) |-> 0 : (nodeList . next)
           </ heap > 
           < form > A === (?A @ [?vit]) </ form > </ config > */
    
    /*@ assert < config > < env > iterx |-> ?ix itery |-> ?iy x |-> x0 y |-> ?y </ env > < heap > list(x0)(A) list(?y)(A) </ heap > < form > TrueFormula </ form > </ config > */
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


/*@ var ?y ?ix ?iy ?vit ?v : ?Int */
/*@ var x0 : FreeInt */
/*@ var ?A ?B ?C : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
