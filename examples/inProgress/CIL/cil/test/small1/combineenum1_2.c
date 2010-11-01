extern enum {
  INT = 0,
  FLOAT = 3,
} x1;

#include "testharness.h"

int main() {
  foo(); /* Set x1 */
  if(FLOAT != 3 || x1 != 1) E(1);

  SUCCESS;
}
