#include <stdlib.h>
#include <stdio.h>

int gcd(int x, int y)
{
  int z;
  int c;

  if(y > 0)
  {
    c = 0;
    z = x;
    
    while (x >=y )
    {
      x -= y;
      c = c + 1;
    }
    z = y;
    y = x;
    x = z;
    gcd(x,y);
  }
  return x;
}

int main()
{
  gcd(100,44);
  printf("%d\n",gcd(100,44));
  return 0;
}

