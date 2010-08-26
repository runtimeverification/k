#include <stdio.h>

int x;

int main(int argc, char **argv)
{
  x = 2;
  if (argc)
    x = -x;
  printf("hello world - %d args, and x is %d\n", -argc, x);
  return 0;
}
