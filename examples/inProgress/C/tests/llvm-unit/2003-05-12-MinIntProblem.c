#include <stdio.h>

void foo(int X) {
  if (X+1 < 0)
    printf("success\n");
}
int main() {
 foo(-2147483648);
 return 0;
}

