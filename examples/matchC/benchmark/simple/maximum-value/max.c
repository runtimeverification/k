#include <stdlib.h>

int max(int x, int y)
{
  int z;
  if (x < y) z = y;
  else z = x;
  return z;
}


int main()
{
  int x;
  int y;
  x = 8;
  y = 45;
  x = max(x,y);
  return 0;
}


