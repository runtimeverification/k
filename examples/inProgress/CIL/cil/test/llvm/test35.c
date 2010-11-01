#include <stdio.h>

char s1[] = "aa", s2[] = "bb";

long s[] = { (long)s1, (long)s2 };

int main(int argc, char **argv)
{
  char *fun = (char *)s[1];

  printf("hello world %ld %ld\n", fun[0], fun[2]);
  return 0;
}
