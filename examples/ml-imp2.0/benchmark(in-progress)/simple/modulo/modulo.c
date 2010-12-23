#include <stdlib.h>
#include <stdio.h>

int modulo(int x, int y)
{
  while (x >=y )
  {
    x -= y;
  }
  return x;
}

int modulo2(int x, int y)
/*@ pre < config >
           < env > x |-> x0  y |-> y0 </ env >
           < heap > (.).Map </ heap >
           < form > TrueFormula </ form > </ config > */
/*@ post < config >
           < env > ?rho </ env >
           < heap > (.).Map </ heap >
           < form > returns ?result /\ (?result === x0 %Int y0) </ form > </ config > */
{
  int result;
  if (x >= y) result = modulo2((x-y),y);
  else result = x;
  return result;
}

/*@ verify */
int main()
{
  int x;
  int y;
  x = 5;
  y = 2;
  printf("%d %d\n",x,y);
/*@ assert < config >
           < env > x |-> 5  y |-> 2 </ env >
           < heap > (.).Map </ heap >
           < form > TrueFormula </ form > </ config > */
  x = modulo2(x,y);
  printf("%d \n",x);
/*@ assert < config >
           < env > x |-> ?x y |-> 2 </ env >
           < heap > (.).Map </ heap >
           < form > ?x === (5 %Int 2) </ form > </ config > */  
  return 0;
}


/*@ var ?x ?d ?result : ?Int */
/*@ var x0 y0 : FreeInt */
/*@ var ?rho : ?MapItem */
/*@ var C : FreeBagItem */

