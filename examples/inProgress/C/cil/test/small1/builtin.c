#include "testharness.h"

int main() {
  double d = __builtin_fabs(-2.0);
  printf("Result is %lf\n", d);
  SUCCESS;
}
