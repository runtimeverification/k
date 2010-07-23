#include "testharness.h"

int main () {
  int x = 5;
  x = 42;     //CIL is moving this below the definition of i
  int i = x;
  if (i != 42) E(99);
  
  SUCCESS;
}
