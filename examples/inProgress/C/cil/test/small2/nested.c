// example of a situation where nested areas are registered

#include <stdio.h>     // printf

struct Foo {
  int a;
  int b[8];
} foo [16];

int main()
{
  struct Foo *f = foo;
  int i;
  int acc = 0;

  printf("start of nested\n");

  for (i=0; i<16; i++) {
    int *b = f[i].b;
    b += 2;
    b[0] = 3;
    b[1] = 4;
    acc += b[1] - b[0];
  }

  printf("end of nested\n");

  return acc - 16;
}

