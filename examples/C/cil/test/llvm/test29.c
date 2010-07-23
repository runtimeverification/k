#include <stdio.h>

int a = 1, b = 2;
int *s[] = { &a, &b };

int main(int argc, char **argv)
{
  *s[0] = 22;
  printf("hello world %d %d\n", a, b);
  return 0;
}
