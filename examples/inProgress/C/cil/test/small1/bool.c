#include "testharness.h"

int main()
{
  _Bool x = 1;
  int z = 2;
  double zz = 0.0;

  if (!x) E(1);

  x = z;
  if (!x) E(2);
  if (x != 1) E(3);

  x = zz;
  if (x) E(4);

  if ((_Bool)2 != 1) E(5);
  if ((_Bool)(1.0 + 2) != 1) E(6);

  SUCCESS;
}
