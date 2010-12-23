#include <stdlib.h>
#include <stdio.h>

int gcd(int x, int y)
/*@ pre < config > < env > x |-> x0 y |-> y0  </ env >
                   < heap > (.).Map </ heap >
                   < form > TrueFormula </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > (.).Map </ heap >
                    < form > returns ?x /\ (?x === greatestcd(x0,y0)) </ form >
                    C </ config > */
{  
  int z;
  int c;

  if(y > 0)
  {
    x = gcd(y,(x % y));
  }
  
  return x;
}

int main()
{
  gcd(100,44);
  printf("The gcd for %d and %d is %d\n",100,44,gcd(100,44));
  return 0;
}

/*@ var ?z ?x ?c : ?Int */
/*@ var x0 y0 : FreeInt */
/*@ var ?rho : ?MapItem */
/*@ var C : FreeBagItem */
