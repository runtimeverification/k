#include "testharness.h"

int f(int );
int s(int );
int d(double );

int main() {

  {
    int x1 = f(5);
    if(x1 != 5) E(1);
  }

  {
    int x2 = f(256);
    if(x2 != 0) E(2);
  }

  {
    int x3 = s(65536 + 1);
    if(x3 != 1) E(3);
  }

  {
    int x4 = d(1);
    if(x4 != 1) E(4);
  }

  SUCCESS;
  
}

// It appears that here the unsigned char takes precedence
int f(x)
  unsigned char x;
{
  return x;
}

int s(x)
     short x;
{
  return x;
}

int d(x)
     float x;
{
  return x;
}
