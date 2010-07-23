#include "testharness.h"

/* Test that we rename properly inlines even if they have prototypes and
   if they are used before they are defined */
int foo(int x); /* Declare it here.  */

inline int foo(int x) { return x; } 

extern getfoo2();

int main() {
  if(getfoo2() != (int)foo) {
    printf("Merging of inlines did not work\n");
    E(1);
  }

  SUCCESS;
}
