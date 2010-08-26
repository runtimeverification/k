#include "testharness.h"

long z;
int zz;

int main()
{
  long x1 = 2L * (z * 0);
  long x2 = 2L * (z & 0);
  long x3 = 2L * (0 << zz);
  long x4 = 2L * (0 >> zz);

  printf("%ld\n", x1);
  printf("%ld\n", x2);
  printf("%ld\n", x3);
  printf("%ld\n", x4);
  if (x1 != 0) E(1);
  if (x2 != 0) E(2);
  if (x3 != 0) E(3);
  if (x4 != 0) E(4);

  SUCCESS;
}
