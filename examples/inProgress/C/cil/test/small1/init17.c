#include "testharness.h"

static int f()
{
  return 0x101;
}

int c0 = (char)257;

int main(int argc, char **argv)
{
  int c1 = (char)f();
  int c2;
  int c3 = (char)257;
  c2 = (char)f();
  printf("Should be 1: c0=%d, c1=%d, c2=%d, c3=%d\n", c0, c1, c2, c3);
  if(c0 != 1) E(1);
  if(c1 != 1) E(2);
  if(c2 != 1) E(3);
  if(c3 != 1) E(4);
  SUCCESS;
}
