#include "testharness.h"

int main() {
  long long x = 8LL;

  if(x != 8) E(1);

  SUCCESS;
}
