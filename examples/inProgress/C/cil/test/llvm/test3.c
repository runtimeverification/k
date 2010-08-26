#include <stdio.h>

int f(void)
{
  int a[20];

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
