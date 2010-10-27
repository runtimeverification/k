#include <stdio.h>

int x;
char y;

int main(int argc, char **argv)
{
  y = 7;
  x = y;
  if (argc)
    x = -x;
  printf("hello world - x is %d\n", x);
  return 0;
}
