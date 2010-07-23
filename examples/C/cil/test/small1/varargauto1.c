#include "testharness.h"
#include <stdio.h>
#include <stdarg.h>

// A test case with automatic vararg descriptors
struct foo {
  int f;
};
// This will be passed char*, int*, int and struct foo*
#define AN_INT     0
#define AN_STR 1
#define AN_INTPTR  2
#define AN_FOOPTR  3

void myva1(int many, ...);

int main() {
  struct foo x = { 1 } , y = { 2 };
  struct foo *px = &x, *py = &y;
  
  myva1(4, AN_INT, 5,
           AN_STR, "hello",
           AN_STR, "world",
           AN_INTPTR, &px->f);
  SUCCESS;
}


void myva1(int many, ...) {
  int count;
  va_list marker;

  va_start(marker, many);
  for(count=0;count<many;count++) {
    int tag = va_arg(marker, int);
    switch(tag) {
    case AN_INT:
      {
        int data = va_arg(marker, int);
        printf("An_int: %d\n", data);
        break;
      }
    case AN_STR:
      {
        char* data = va_arg(marker, char*);
        printf("An_str: %s\n", data);
        break;
      }
    case AN_INTPTR:
      {
        int* data = va_arg(marker, int*);
        printf("An_intptr: %x (%d)\n", (long)data, *data);
        break;
      }
    case AN_FOOPTR:
      {
        struct foo* data = va_arg(marker, struct foo*);
        printf("An_fooptr: %d\n", data->f);
        break;
      }
    }
  }
}
