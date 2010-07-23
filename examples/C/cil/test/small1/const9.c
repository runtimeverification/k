#include "testharness.h"

int glob;
int globarray[(sizeof(void *) == sizeof(void *)) ? 4 : (int)&glob];

struct foo {
  int f1, f2, f3;
};

int arr1[9 * (int)(&((struct foo*)0)->f3)];

int main() {
  int x=5,y;

  int array[(sizeof(void *) == sizeof(void *)) ? 4 : y];
  
  switch (x) {
    
  case ((sizeof(void *) == sizeof(void *)) ? 4 : y ):
    break;
  }
  SUCCESS;
}
