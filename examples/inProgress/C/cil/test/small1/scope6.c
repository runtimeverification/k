#include "testharness.h"

struct foo {
  int x;
  int y;
} foo;

int main() {

  typedef struct foo *PFOO;

  PFOO pfoo = &foo;
  
  struct foo {
    int a;
    int b;
  } anotherfoo;

  int z = pfoo->x + anotherfoo.a; // This means that PFOO refers to the outer type

  SUCCESS;
}
