#include <stdio.h>

char *s[] = { "fun", "baz" };

int main(int argc, char **argv)
{
  printf("hello world %d %d %s\n", s[0][0], s[0][1], s[1]);
  return 0;
}
