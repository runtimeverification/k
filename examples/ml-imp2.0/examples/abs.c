#include <stdlib.h>
#include <stdio.h>

int absolute(int n)
/*@ pre < config > < env > n |-> n0 </ env >
                    < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < form > returns ?n /\ (?n === abs(n0)) </ form >
                    C </ config > */
{
  if (n < 0) n = 0 - n;
  return n;
}

int main()
{
  int n;
  n = 1000;
  absolute(n);
  n = -456;
  absolute(n);
  return 0;
}

/*@ var ?n : ?Int */
/*@ var n0 : FreeInt */
/*@ var ?rho : ?MapItem */
/*@ var C : FreeBagItem */
