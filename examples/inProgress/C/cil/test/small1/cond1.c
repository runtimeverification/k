#include "testharness.h"

int foo() {
  return 5;
}

int main() {

  int x1 = ({goto L1; 0;}) && ({L1: 5;});

  printf("x1 = %d\n", x1);

  if(x1 != 1) E(1);

  {
    int x2 = 0 && ({L2: 5;});
    if(x2 != 0) E(2);
  }

  {
    int x3 = 0 || 5;
    printf("x3 = %d\n", x3);
    if(x3 != 1) E(3);
  }
  
  {
    int x4 = 0 || foo();
    printf("x4 = %d\n", x4);
    if(x4 != 1) E(4);
  }
  
  SUCCESS;
}
