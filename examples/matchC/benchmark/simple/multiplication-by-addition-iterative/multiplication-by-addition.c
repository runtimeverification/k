#include <stdlib.h>
#include <stdio.h>

int multiply(int x, int y)
{
  int q;
  int i;
  q = 0;
  i = 0;
  
  while(i < y )
  {
        q = q + x;
        i = i + 1;
  }
  
  return q;
}

int main()
{
  int m;
  m = multiply(3,4);
  return 0;
}


