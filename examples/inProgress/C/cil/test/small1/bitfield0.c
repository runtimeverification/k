#include "testharness.h"

struct {
  int x;
  int y : 2;
  int z : 4;
} g;

int main() {

  g.y = 113;
  if(g.y != 113 % 4) E(1);
  g.z = 113;
  if(g.z != 113 % 16) E(2);

  SUCCESS;
}
