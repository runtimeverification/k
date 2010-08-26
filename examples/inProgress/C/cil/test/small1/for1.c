#include "testharness.h"

int main() {
  int z;
  for(int i = 0, j = 5; i <= 3 && j >= 3; i ++, j --, z = i) {
    i += j - 3;
  }
  if(z != 5) E(1);

  SUCCESS;
}
