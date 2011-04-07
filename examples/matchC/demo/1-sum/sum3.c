#include <stdlib.h>
#include <stdio.h>


int sum(int n)
/*@ req n = n0 /\ n >= 0
    ens returns((n * (n + 1)) / 2) */
{
  int s;

  s = 0;
  //@ invariant s = ((n0 - n) * (n0 + n + 1)) / 2 /\ n >= 0
  while (n > 0)
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
  printf("The sum for the first 10 natural numbers: %d\n", s);

  //@ assert <out> [55] </out>
  return 0;
}

