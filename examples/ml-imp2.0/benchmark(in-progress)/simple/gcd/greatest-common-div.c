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
    c = 0;
    z = x;
/*@ invariant < config > < env > x |-> ?x y |-> y0 c |-> ?c z |-> ?z </ env >
                      < heap > (.).Map </ heap >
                      < form > ?z === (y0 *Int ?c +Int ?x) </ form > C </ config > */
    while (x >=y )
    {
      x -= y;
      c = c + 1;
    }
    z = y;
    y = x;
    x = z;
    gcd(x,y);
  }
  return x;
}

int main()
{
  gcd(100,44);
  printf("%d\n",gcd(100,44));
  return 0;
}

/*@ var ?z ?x ?c : ?Int */
/*@ var x0 y0 : FreeInt */
/*@ var ?rho : ?MapItem */
/*@ var C : FreeBagItem */
