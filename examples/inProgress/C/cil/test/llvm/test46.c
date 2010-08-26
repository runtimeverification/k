#include <stdio.h>

int a[10][20];
int (*b)[20] = a;

int f(void)
{
  int i, sum = 0;

  for (i = 0; i < 20; i++)
    b[1][i] = i * 2;

  for (i = 5; i < 15; i++)
    sum += a[1][i];

  return sum;
}

int main(int argc, char **argv)
{
  int zz = f();
  printf("%d\n", zz);
  return 0;
}
