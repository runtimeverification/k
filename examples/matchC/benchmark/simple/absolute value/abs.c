#include <stdlib.h>
#include <stdio.h>

int absolute(int n)
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

