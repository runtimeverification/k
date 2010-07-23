#include "testharness.h"

// Test the handling of no-prototype functions

int main() {
  int *x, *y;
  
  int *res = &x; // Make res like x

  // Call with the wrong number of arguments
  res = noprotofun(&x);
  
  SUCCESS;
}
