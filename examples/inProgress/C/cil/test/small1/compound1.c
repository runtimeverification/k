#include "testharness.h"

int main() {
  unsigned long a;
  unsigned long *p;
  p = (unsigned long *)&p;
  a = ++(*p);
  if (a-1 != (unsigned long)&p)
    E(1);
  SUCCESS;
}
