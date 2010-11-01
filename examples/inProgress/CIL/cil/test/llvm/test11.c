#include <stdio.h>

int x;
char y;
double z;

int main(int argc, char **argv)
{
  y = 7;
  x = -y;
  if (!z)
    x = -x;
  printf("hello world - x is %d\n", x);
  return 0;
}
