#include "testharness.h"

/* Test that we do not share too many inlines */
static int g;
static inline int foo(int x) { return g; }

extern int getfoo2();


int main() {
  if(getfoo2() == (int)foo)  E(1);
  SUCCESS;
}
