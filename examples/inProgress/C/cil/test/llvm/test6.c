#include <stdio.h>

int a[20];

int f(void)
{
  int *b = a;

  b[0] = 33;
  b[2] = 19;

  return b[2];
}

int main(int argc, char **argv)
{
  int zz = f();
  printf("%d\n", zz);
  return 0;
}
