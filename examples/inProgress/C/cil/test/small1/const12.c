#include "testharness.h"

int main()
{
  int x = -(unsigned char)1;

  printf("%d\n", x);
  if (x != -1) E(1);

  SUCCESS;
}
