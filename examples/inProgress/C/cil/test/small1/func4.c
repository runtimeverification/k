typedef struct {
  int (*f)(int);
} FOO;

int highorder(int a(int), int arg) {
  return a(arg);
}

int incr(int x) {
  return x + 1;
}
#include "testharness.h"

int main() {
  if(highorder(incr, 5) != 6) E(1);

  {
    FOO x = { incr };
    if(x.f(6) != 7) E(2);
  }

  SUCCESS;
  
}
