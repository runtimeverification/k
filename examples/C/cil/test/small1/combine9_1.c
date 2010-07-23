/* We have two incompatible definitions of g
 * The struct looks the same if you do not unroll the typedef */
#include "testharness.h"

typedef int INT;

struct {
  INT i;
  int x;
} g;


int main() {
  E(1); /* Should not compile */
}
