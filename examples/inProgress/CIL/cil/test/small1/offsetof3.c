#include "testharness.h"
#include <stddef.h>

// same as offsetof2.c, but uses gcc's __builtin_offsetof

struct foo {
  struct bar {
    int a[8];
    int b;
  } f1;
  struct baz {
    int c[4];
  } f2[2];
};

//Make "f2" a typedef as well as a field, and make sure that doesn't break 
// anything.  This was a bug for Roberto Bagnara.
typedef struct foo f2;

int main() {

  // Test for gcc's __builtin_offsetof, which we handle specially

  if(__builtin_offsetof(struct foo, f1.b) != 8 * sizeof(int)) E(1);

  if(__builtin_offsetof(struct foo, f1.a[2]) != 2 * sizeof(int)) E(2);

  if(__builtin_offsetof(f2, f2[1].c[3])
     != sizeof(struct bar) + sizeof(struct baz) + 3 * sizeof(int)) E(3);

  if(__builtin_offsetof(f2, f2) != sizeof(struct bar)) E(4);

  SUCCESS;
}
