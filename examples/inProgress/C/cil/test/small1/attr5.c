#include "testharness.h"

int x;
int * myfunc(void) __attribute__((section(".modinfo"))) {
  return &x;
}

int main() {
  if(&x != myfunc()) E(1);
  
  SUCCESS;
}
