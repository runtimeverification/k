#include <stdlib.h>

int refact(int n)
{
  int res;
  res = 1;
  if (n > 1)
  {
    res = res * refact(n - 1) ;
  }
  return res;
}

int main()
{
  int f;
  f = refact(10);
  return 0;
}


