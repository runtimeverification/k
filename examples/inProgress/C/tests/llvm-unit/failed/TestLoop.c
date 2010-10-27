#include <stdio.h>

int foo(int i, int j) {
  printf("%d\n", j);
  return j;
}


int main(int level) {
    int i;
    int fval[4];
    //for (i = 3; i < 10; i--)

    for (i = 3; i >= 0; i--)
      fval[i] = foo(level - 1, level*4 + i + 1); 

    for (i = 0; i < 4; ++i)
      foo(0, fval[i]);
    return 0;
}
