#include "testharness.h"

typedef struct foo *PFOO;

typedef struct foo {
  int x;
  PFOO y;
} *PTR;

PTR g3;

int main() {
  main2();
  /* Make sure that the offset is right */
  if(& g3->y != & ((struct { int x; PFOO y;} *)g3)->y) E(1);

  SUCCESS;
}
