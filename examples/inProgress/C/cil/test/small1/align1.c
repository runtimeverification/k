#include "testharness.h"


struct testalign {
  int f1;
} __attribute__((__aligned__(16)));

struct t1 {
  int f0;
  struct testalign a;
};

int main() {
  int offset;

  offset = &((struct t1*)0)->a.f1;
  printf("Offset is: %d\n", offset);

  if ((int)&(( struct t1  *)0)->a.f1 & 15) {
    E(1);
  }


  SUCCESS;
}
