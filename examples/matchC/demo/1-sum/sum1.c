#include <stdlib.h>
#include <stdio.h>


int sum(int n)
{
  int s;

  s = 0;
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

  return 0;
}
