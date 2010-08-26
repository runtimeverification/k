#include "testharness.h"

// From c-torture

// First an extern inline definition
extern __inline__ int
odd(void)
{
  return 1;
}

// Now a use of that definition
int
odd1(void)
{
  // We always use the last definition if we do not optimize
  // And we use the last extern __inline__ definition when we
  // do optimize

  // IN CIL WE ALWAYS OPTIMIZE. SO YOU BETTER DEFINE EQUIVALENT
  // BODIES in the extern inline and in the real definition
  return odd(); 
}


// And now a definition without the inline
int
odd(void)
{
  return 3;
}


int main() {
  { int x = odd(); if(x != 3) E(1); }

  {
    int y = odd1();
    if(y != 1) E(2);
  }

  SUCCESS;
}
