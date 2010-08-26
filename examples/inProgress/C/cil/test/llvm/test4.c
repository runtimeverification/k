#include <stdio.h>

int a[20];

int f(void)
{
  a[0] = 33;
  a[2] = 19;

  return a[2];
}

int main(int argc, char **argv)
{
  int zz = f();
  printf("%d\n", zz);
  return 0;
}
