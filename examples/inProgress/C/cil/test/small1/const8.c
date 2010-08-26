#include "testharness.h"

int main() {
  unsigned base = 5;
  unsigned long max = (unsigned long) -1 / base;

  unsigned long max1 = (unsigned long) -1;
  printf("max = %ld, max1 = %ld\n", max, max1 / base);

  if(max != max1 / base) E(1);
  
  SUCCESS;
}


