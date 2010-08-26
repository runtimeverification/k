#include "testharness.h"

int main() {
  int x;
  int *p = 0;
  x = 1;
  if(x || *p) { // Do not check p if x = 1
    x = 0;
  }
  if(x && *p) { // Do not check p if x = 0
    E(1);
  }
  SUCCESS;
}
