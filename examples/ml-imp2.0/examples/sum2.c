#include <stdlib.h>
#include <stdio.h>

int sum(int n)
/*@ pre  < config > < env > n |-> n0 </ env >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < form > returns ((n0 *Int (n0 +Int 1)) /Int 2) </ form >
                    C </ config > */
{
  int s;
  s = 0;
  /*@ invariant < config > 
                < env >
                  n |-> ?n
                  s |-> ((n0 +Int (-Int ?n)) *Int (n0 +Int ?n +Int 1)) /Int 2
                </ env >
                < form > TrueFormula </ form >
                C </ config > */
  while (n)
  {
    s += n;
    n -= 1;
  }
  return s;
}

int main()
{
  int s;
  s = sum(10);
  printf("The sum for the first 10 natural numbers: %d\n", sum(10));
  return 0;
}


/*@ var ?s ?n : ?Int */
/*@ var n0 : FreeInt */
/*@ var ?rho : ?MapItem */
/*@ var C : FreeBagItem */

