#include <stdio.h>
#include <stdarg.h>

int blah(void);

double sum(int s0, ...)
{
  va_list args;
  double s = s0, n;

  va_start(args, s0);
  while (n = va_arg(args, int))
    s += n;
  va_end(args);

  return s;
}

int main(int argc, char **argv)
{
  double x = sum(4, 3, 32, 22, 0);
  printf("hello world %f\n", x);
  return 0;
}
