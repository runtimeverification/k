#include "testharness.h"

/* Test that we remove duplicate inline functions */
inline int foo(int x) {
  return x;
}

extern int getfoo2();

int main() {
  if(getfoo2() != (int)foo)  E(1);

  SUCCESS;
}
