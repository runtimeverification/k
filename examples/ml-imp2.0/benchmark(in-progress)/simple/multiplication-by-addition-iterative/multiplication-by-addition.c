#include <stdio.h>

int multiply(int x, int y)
/*@ pre  < config > < env > x |-> x0 y |-> y0 </ env >
                    < form > @(x0 >=Int 0) /\ @(y0 >=Int 0) </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < form > returns (x0 *Int y0) </ form >
                    C </ config > */
{
  int q;
  int i;
  q = 0;
  i = 0;
/*@ invariant < config > 
              < env > x |-> x0 y |-> y0 q |-> ?q i |-> ?i </ env >
              < form > ?q === (?i *Int x0) </ form >
              C </ config > */
  while(i < y )
  {
        q = q + x;
        i = i + 1;
  }
/*@ assert < config > 
              < env > x |-> x0 y |-> y0 q |-> ?q i |-> ?i </ env >
              < form > ?q === (?i *Int x0) /\ (?i === y0) </ form >
              C </ config > */
  return q;
}

int main()
{
  int m;
  m = multiply(3,4);
  printf("The numbers are: %d and %d and the result of their multiplication is: %d\n",3,4,m);
  return 0;
}


/*@ var ?q ?i : ?Int */
/*@ var x0 y0 : FreeInt */
/*@ var ?rho : ?MapItem */
/*@ var C : FreeBagItem */

