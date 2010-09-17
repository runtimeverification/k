kmod TEST is including IMP-SYNTAX + LIST-HP
  syntax Id ::= nodeList | next | val | x | y | p | reverse
  syntax ?Int ::= `?x | `?p
  syntax ?Seq ::= `?B | `?C 
  syntax FreeSeq ::= `A

  syntax Decl ::= test


  macro test = (

struct nodeList {
  int val;
  struct nodeList *next;
};


int reverse(struct nodeList *x;)
/* pre < config > 
          < env > x |-> [?x : struct nodeList *] </ env > 
          < heap > list(?x)(A) </ heap > 
          < form > TrueFormula </ form > 
          </ config > */
/* post < config > 
          < env > .Map </ env >
          < heap > list(?x)(rev(A)) </ heap > 
          < form > ?return(?x) </ form > 
          </ config > */
{
  struct nodeList *p;
  struct nodeList *y;
  p = 0 ;
  /* invariant < config > 
                      < env > p |-> [?p : struct nodeList *] x |-> [?x : struct nodeList *] </ env >
                      < heap > list(?p)(?B) list(?x)(?C) </ heap >
                      < form > rev(A) === rev(?C) ::: ?B </ form > 
                      </ config > */
  while(x != 0) {
    y = *(x + 1); --- x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}

void main()
{
  /* assume < config > < env > x |-> [?x : struct nodeList *] </ env > < heap > list(?x)(A) </ heap > < form > TrueFormula </ form > </ config > */
  x = reverse(x) ;
  /* assert < config > < env > x |-> [?x : struct nodeList *] </ env > < heap > list(?x)(rev(A)) </ heap > < form > TrueFormula </ form > </ config > */
}
  ) 
endkm

