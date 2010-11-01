#include <stdio.h>

unsigned short a = 50336, b = 1995;

int sum(void)
{
  return a + b;
}

int main(int argc, char **argv)
{
  printf("hello world %d\n", sum());
  return 0;
}
