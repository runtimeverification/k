struct { int f; } x; // Read-write

#include "testharness.h"

int main() {
  x.f = 5; // Now write to it
  if(read() != 5) E(1);

  SUCCESS;
}
