typedef struct foo PSFOO;
extern struct foo {
  struct foo * left;
  PSFOO * right;
  int x;
} g;

#include "testharness.h"

int main() {
  printf("Address is %x\n", &g); /* Make sure we use g */
  SUCCESS;
}
