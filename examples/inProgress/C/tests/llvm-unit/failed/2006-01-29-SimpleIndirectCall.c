// PR704

#include <stdio.h>

void hello() {
  printf("Hello, world!\n");
}

void goodbye() {
  printf("Goodbye, world!\n");
}

int main(int argc, char **argv) {
  void (*f)() = (argc > 1) ? &hello : &goodbye;
  f();
  return 0;
}

