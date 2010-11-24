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

/*@ verify */
int main()
{
  int x;
  int y;
  x = 5;
  y = 2;
/*@ assert < config >
           < env > x |-> 5  y |-> 2 </ env >
           < heap > (.).Map </ heap >
           < form > TrueFormula </ form > </ config > */
  x = modulo(x,y);
/*@ assert < config >
           < env > x |-> ?x y |-> 2 </ env >
           < heap > (.).Map </ heap >
           < form > ?x === moduloo(5,2) </ form > </ config > */  
  return 0;
}


/*@ var ?x ?d : ?Int */
/*@ var x0 y0 : FreeInt */
/*@ var ?rho : ?MapItem */
/*@ var C : FreeBagItem */

