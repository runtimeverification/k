#include "testharness.h"

/* An argument whose type is a function should be turned into a function 
 * pointer */

int foo(int x()) {
  return x();
}

// A prototype. This should work but right now it does not because of the
// way abs_direct_decl is defined in cparser.mly. If we use the definition
// from the book we get conflicts
int bar(int ());

