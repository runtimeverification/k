#include <stdlib.h>
#include <stdio.h>

int modulo(int x, int y)
{
  while (x >=y )
  {
    x -= y;
  }
  return x;
}


int main()
{
  int x;
  int y;
  x = 5;
  y = 2;
  
  x = modulo(x,y);
  return 0;
}


