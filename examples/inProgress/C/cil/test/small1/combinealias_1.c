#include <stdio.h>

void __foo(int x) {
  printf("Hello, world!  %d\n", x);
}

void foo(int x) __attribute__((__alias__("__foo")));;
