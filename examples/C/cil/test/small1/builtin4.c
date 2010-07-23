#include "testharness.h"

int main() {
  int l = __builtin_strlen("yoohoo");
  printf("Result is %d\n", l);
  SUCCESS;
}
