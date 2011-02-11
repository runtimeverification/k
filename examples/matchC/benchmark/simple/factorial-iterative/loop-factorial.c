#include <stdlib.h>

int fact(int n)
{
  int res;
  int iterator;
  iterator = 1;
  res = 1;
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
  return 0;
}


