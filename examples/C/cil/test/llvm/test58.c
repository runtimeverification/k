#include <stdio.h>

float a = 3;

void f(double x)
{
  printf("hello %g\n", x);
}

int main(int argc, char **argv)
{
  f(a);
  return 0;
}
