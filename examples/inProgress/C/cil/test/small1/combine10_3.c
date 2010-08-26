#include "testharness.h"

extern struct foo {
  struct foo * left, * right;
  int x;
} g1, g2;


int main() {
  g1 = g2;
  SUCCESS;
}
