#include "testharness.h"

// Test the handling of no-prototype functions

int main() {
  int *x, *y;
  
  int *res = &x; // Make res like x

  res = noprotofun(&x + 1, &y);
  // Try to read from x and y
  if(res != &x + 1) { E(1); }
  
  SUCCESS;
}
