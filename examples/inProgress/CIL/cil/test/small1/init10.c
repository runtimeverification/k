#include "testharness.h"

typedef int tint;


struct foo {
  int other;
  int tint; // Reuse the typedef name
} x = { tint : 5 };


int main() {
  if(x.tint != 5) E(1);
  if(x.other != 0) E(2);

  SUCCESS;
}

