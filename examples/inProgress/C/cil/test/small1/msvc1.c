
#include "testharness.h"

extern "C" {
  int foo(void);

  int bar(void) {
    return 1;
  }
}

extern "C" const int *global = 0;


int main() {
  return 0;
}
