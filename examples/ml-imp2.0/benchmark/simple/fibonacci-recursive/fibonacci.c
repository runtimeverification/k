#include <stdlib.h>

int fibonacci(int n)
{
  int res;
  if (n <= 1) res = 1; 
  else res =  fibonacci(n - 1) + fibonacci(n - 2);
  return res;
}

int main()
{
  int f;
  f = fibonacci(3);
  return 0;
}


