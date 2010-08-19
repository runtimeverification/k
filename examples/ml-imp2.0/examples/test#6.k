kmod TEST is including IMP-SYNTAX + LIST-HP
  syntax Id ::= nodeList | next | val | leng | a | l
  syntax FreeInt ::= `a0
  syntax FreeSeq ::= `A
  syntax !MapItem ::= `!H

  syntax Decl ::= test


  macro test = (

struct nodeList {
  int val;
  struct nodeList *next;
};


int leng(struct nodeList *a;)
/* pre <config> 
          <env> a |-> [a0 : &struct nodeList]  </env> 
          <heap> list(a0)(A) !H  </heap> 
          <form> TrueFormula </form> 
          </config> */
/* post <config> 
          <env> a |-> [a0 : &struct nodeList] l |-> [len(A) : int] </env>
          <heap> list(a0)(A)  !H </heap> 
          <form> ?return(len(A)) </form> 
          </config> */
{
  int l;
  l = -1;
  if (a == 0)  l=0;
  else
  {
  l = 1 + leng(a->next) ;
  }
  return l;
}
) 
endkm