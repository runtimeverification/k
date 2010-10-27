#include <stdio.h>
#define NUM 32

int Array[];
int Array[NUM];
int Foo;            /* If writing to the wrong "Array", this will get clobbered */

int main() { 
  unsigned i;
  for (i = 0; i != NUM; ++i)
    Array[i] = 5;

  printf("%d\n", Foo);
  return 0;
}

