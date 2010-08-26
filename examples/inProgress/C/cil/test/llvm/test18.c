#include <stdio.h>

void silly(int *w)
{
  (*w)++;
}

int main(int argc, char **argv)
{
  int zz = 9;

  silly(&zz);

  printf("hello world - %d\n", zz);
  return 0;
}
