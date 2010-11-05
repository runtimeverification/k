#include "testharness.h"
 
struct foo {
  int a,b;
};

//The length should be 5, not 3.
static struct foo foos[]={
 {1},
 {},
 {3,4},
 {},
 {}
};

int main() {
  printf("sizeof foos = %d.\n", sizeof(foos));

  if (sizeof(foos) != 5*sizeof(struct foo)) E(1);
  if (foos[2].b != 4) E(2);
  if (foos[4].b != 0) E(3);
  
  return 0;
}
