#include <stdio.h>
#include <stdlib.h>

void f(int x, int y) {
  printf("wow\n");
}

void g(int x, int y) {
  printf("yippie!\n");
}

#define FUNC(x, y) ({ f((x), (y)); g((x), (y)); })

#define NUMBER 1

int k(int a) {

  int x, y, z;  
  z = 0;
  FUNC(NUMBER, z);
  return 1;
}

int main(int argc, char** argv) {
  k(5);
  return 0;
}
