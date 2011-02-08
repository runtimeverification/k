#include <stdlib.h>
#include <stdio.h>

int sum(int n)
/*@ pre  n = n0 /\ n0 >= 0 */
/*@ post returns((n0 * (n0 + 1)) / 2) */
{
  int s;
  s = 0;
  /*@ invariant s = ((n0 - n) * (n0 + n + 1)) / 2 /\ n >= 0 */
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
  printf("The sum for the first 10 natural numbers: %d\n", sum(10));
  return 0;
}

/* var n : Int */
/*@ var n0 : FreeInt */

