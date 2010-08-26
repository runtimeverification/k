#include "testharness.h"

// Test the handling of no-prototype functions

int main() {
  int *x, *y;
  
  int *res = &x; // Make res like x

  // Call with integers instead of pointers
  res = noprotofun(5, 6);
  
  SUCCESS;
}
