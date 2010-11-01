#include <stdio.h>

void silly(int *w)
{
  w[1]++;
}

int main(int argc, char **argv)
{
  int zz[2] = { 3, 5};

  silly(zz);

  printf("hello world - %d\n", zz[1]);
  return 0;
}
