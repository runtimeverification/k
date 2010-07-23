#include <stdio.h>

int a[20];

int f(void)
{
  int *b = a;
  int i, sum = 0;

  for (i = 0; i < 20; i++)
    b[i] = i * 2;

  for (i = 5; i < 15; i++)
    sum += a[i];

  return sum;
}

int main(int argc, char **argv)
{
  int zz = f();
  printf("%d\n", zz);
  return 0;
}
