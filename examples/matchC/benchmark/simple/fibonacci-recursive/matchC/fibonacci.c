#include <stdlib.h>

int fibonacci(int n)
// pre  n = n0 /\ (n0 >Int 0)
// post returns(fibon(n0))
{
  if (n <= 1) return 1; 
  else return  fibonacci(n - 1) + fibonacci(n - 2);
}

int main()
{
  int f;
  f = fibonacci(3);
  printf("Fibonacci for 3 is: %d\n", f);

  //@ assert <out> [3] </out>
  return 0;
}

