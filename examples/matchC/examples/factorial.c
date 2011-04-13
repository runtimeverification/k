#include <stdio.h>


int factorial(int x)
//@ rule <k> $ => return fact(x); </k> if x >= 0
{
  int y;

  y = 1;
  //@ invariant fact(old(x)) = y * fact(x) /\ x >= 0
  while (x > 0)
  {
    y *= x;
    x -= 1;
  }

  return y;
}


int main()
{
  printf("10!: %d\n", factorial(10));
  //@ assert <out> [3628800] </out>

  return 0;
}

