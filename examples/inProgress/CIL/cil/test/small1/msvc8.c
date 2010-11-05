#include "testharness.h"

// It turns out that MSVC allows continuation lines
// ... and they are not filtered by the preprocessor
int a = \
0;


int main() {
  if(__LINE__ != 10) E(1);
  
  return a;
}
