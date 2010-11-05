#include <stdio.h>

struct fun {
  int x, y;
};

struct fun a[10][20];
struct fun (*b)[20] = a;

int f(void)
{
  int i, sum1 = 0, sum2 = 0;

  for (i = 0; i < 20; i++)
    b[1][i].x = i * 2;

  for (i = 5; i < 15; i++)
    sum1 += a[1][i].x;

  for (i = 5; i < 15; i++)
    sum2 += b[1][i].x;

  return (sum1 == sum2);
}

int main(int argc, char **argv)
{
  int zz = f();
  printf("%d\n", zz);
  return 0;
}
