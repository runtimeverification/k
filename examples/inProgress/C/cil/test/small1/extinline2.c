#include "testharness.h"

extern inline int f(void) { return 1; }

int g(void)
{
  return f();
}

int f(void) { return 2; }

int h(void)
{
  return f();
}


int main(void)
{
  if (g() != 2) E(1);
  if (h() != 2) E(1);
  SUCCESS;
}
