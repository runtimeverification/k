
kmod P-LIST-REVERSE is including IMP-SYNTAX + LIST-HP
  syntax Id ::= nodeList | next | val | x | y | p | reverse | a | n
  syntax ?Int ::= `?x | `?p
  syntax ?Seq ::= `?B | `?C 
  syntax FreeSeq ::= `A

  syntax Decl ::= pListReverse


  macro pListReverse = (

struct nodeList {
  int val;
  struct nodeList *next;
};

int a;
struct nodeList n;

int reverse(struct nodeList *x;)
// pre < config > < env > x |-> [?x, &struct nodeList] </ env >
                  < heap > list(?x)(A) </ heap > < form > TrueFormula </ form > </ config >
// post < config > < env > (.).Map </ env >
                   < heap > list(?x)(rev(A)) </ heap > < form > ?return(?x) </ form > </ config >
{
  struct nodeList *p;
  struct nodeList *y;
  p = 0 ;
  // invariant < config > < env > p |-> [?p, &struct nodeList] x |-> [?x, &struct nodeList] </ env >
                          < heap > list(?p)(?B) list(?x)(?C) </ heap >
                          < form > rev(A) === rev(?C) ::: ?B </ form > </ config >
  while(x != 0) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}

  ) 
endkm

