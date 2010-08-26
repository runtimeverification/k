#include <stdio.h>

int main(int argc, char **argv)
{
  int x = 2;
  if (argc)
    x = -x;
  printf("hello world - %d args, and x is %d\n", -argc, x);
  return 0;
}
