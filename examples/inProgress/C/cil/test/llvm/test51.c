#include <stdio.h>

int x(void)
{
  int a, b;

  b = 1;
  a = b;
  b = 2;

  return a;
}

int y(void)
{
  int b, a;

  b = 1;
  a = b;
  b = 2;

  return a;
}

int main(int argc, char **argv)
{
  printf("hello world %d %d\n", x(), y());
  return 0;
}
