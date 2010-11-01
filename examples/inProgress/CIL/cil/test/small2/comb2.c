// comb2.c
// part 2/4 of a program expected to be combined

#include "../small1/testharness.h"

static int global_com2 = 5;

int foo2_com2(int x)
{
  return x + global_com2;
}

extern int foo_com3(int x);
extern void hpfy();

int main()
{
  int res1 = foo_com3(6);
  int res2 = foo2_com4(61);
  printf("foo_com3(6): %d\n", res1);
  printf("foo2_com4(61): %d\n", res2);
  if (res1 != (11+sizeof(int*))) E(1);
  if (res2 != 70) E(2);
  hpfy();
  return 0;
}
