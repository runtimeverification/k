#include "testharness.h"

typedef union un {
  int i;
  long long l;
  struct str {
    int i1, i2;
  } s;
} un;

int f(union un x) {
  return x.s.i1;
}

un glob = (un)6;

int main() {
  un x = (un)5LL;
  if(x.l != 5LL) E(1);
  if(x.i != 5) E(2);

  {
    struct str s = { 1, 2 };
    un y = (union un) s;
    if(y.s.i1 != 1 || y.s.i2 != 2) E(3);

    if(f((un)s) != 1) E(4);
  }

  if(glob.i != 6) E(5);
  
  SUCCESS;
}
