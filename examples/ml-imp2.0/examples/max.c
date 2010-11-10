#include <stdlib.h>

int max(int x, int y)
/*@ pre < config > < env > x |-> x0 y |-> y0  </ env >
                   < heap > (.).Map </ heap >
                   < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > (.).Map </ heap >
                    < form > returns ?z /\ @(?z >=Int x0) /\ @(?z >=Int y0) </ form >
                    C </ config > */
{
  int z;
  if (x < y) z = y;
  else z = x;
  return z;
}

/*@ verify */
int main()
{
  int x;
  int y;
  x = 8;
  y = 45;
  x = max(x,y);
  return 0;
}

/*@ var ?z : ?Int */
/*@ var x0 y0 : FreeInt */
/*@ var ?rho : ?MapItem */
/*@ var C : FreeBagItem */
