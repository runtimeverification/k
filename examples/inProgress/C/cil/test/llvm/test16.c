#include <stdio.h>

struct zz {
  int a, b;
};
struct zz x;

int main(int argc, char **argv)
{
  x.a = x.b = 2;
  if (argc)
    x.b += x.a;
  printf("hello world - x.a is %d and x.b is %d\n", x.a, x.b);
  return 0;
}
