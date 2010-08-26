/* test case for Sourceforge bug #1812231 */
#include "testharness.h"

int f(int x)
{
  switch (x) { 
#ifdef CIL
    __blockattribute__(x)
#endif
  case 1:
    return 2;
  }
  return 0;
}

int main()
{
  if (f(1) != 2) E(1);
  SUCCESS;
}

