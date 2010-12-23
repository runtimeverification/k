#include <stdio.h>

int fact(int n)
/*@ pre  < config > < env > n |-> n0 </ env >
                    < form > @(n0 >Int 0) </ form > C </ config > */
/*@ post < config > < env > ?rho </ env >
                    < form > returns (factorial(n0)) </ form >
                    C </ config > */
{
  int res;
  int iterator;
  iterator = 1;
  res = 1;
/*@ invariant  < config > < env > n |-> n0 iterator |-> ?i res |-> ?res </ env >
                    < form > ?res === factorial(?i) </ form > C </ config > */
  while( n >= iterator)
  {
    res = res * iterator;
    iterator += 1;
  }
  return res;
}

int main()
{
  int f;
  f = fact(10);
  printf("Factorial-it of %d is %d\n", 10, f);
  return 0;
}


/*@ var n0 : FreeInt */
/*@ var ?res ?i : ?Int */
/*@ var ?rho : ?MapItem */
/*@ var C : FreeBagItem */

