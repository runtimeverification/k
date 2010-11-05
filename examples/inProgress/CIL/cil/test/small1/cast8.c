#include "testharness.h"

/* A very surprising bug that has surfaced after 3 years */

int main() {
  int base = 5;
  unsigned long max_over_base =
    (unsigned long) -1 / base; 

  unsigned long correct =
    ((unsigned long) -1) / base; 

  printf("Result is %ld. Correct=%ld\n", max_over_base, correct);
  if(max_over_base != correct) E(1);

  SUCCESS;
}
