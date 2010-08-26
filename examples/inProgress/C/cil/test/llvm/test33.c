#include <stdio.h>

char s1[] = "aa", s2[] = "bb";

char *s[] = { s1 + 2 - 1, s2 };

int main(int argc, char **argv)
{
  printf("hello world %d %d\n", s[0][0], s[1][0]);
  return 0;
}
