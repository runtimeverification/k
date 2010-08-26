#include "testharness.h"

typedef int (ide_dmaproc_t)(int, int *);



int test(int x, int *y) {
  return x + *y;
}

struct foo {
  ide_dmaproc_t *dmaproc;
} x = { test };



int main() {
  int y = 7;

  if(x.dmaproc(5, &y) != 12) E(1);
  
  SUCCESS;
}
