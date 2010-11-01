#include "testharness.h"
#include "testkinds.h"

int main() {
  int x __attribute__((foo));
  {
    __blockattribute__ (nobox)
      x ++; // Let's see if CCured sees this
  }
}
