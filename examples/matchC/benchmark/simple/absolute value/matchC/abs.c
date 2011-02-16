#include <stdlib.h>
#include <stdio.h>

int absolute(int n)
//@ pre <env> n |-> n0 </env>
//@ post returns(n) /\ (((n = n0) /\ (n >= 0)) \/ ((n = -n0) /\ (n < 0)))
{
  if (n < 0) n = -n;
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
