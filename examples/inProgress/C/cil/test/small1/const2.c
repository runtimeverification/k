#include "testharness.h"

int main() {
  unsigned int x = (unsigned)0 - 1;
  
  if((x >= 0) == 0) E(1);

  if (((unsigned)0 - 1 >= 0) == 0)
    E(2);

  SUCCESS;

  return 0;
}
