/* We test that we rename properly the name of enumeration items */
enum e1 {
  ITEM1 = 0,
  ITEM2 = 1,
} x1;

extern int getitem5();

#include "testharness.h"

int main() {
  x1 = ITEM1;
  if(x1 != 0) E(1);
  if(getitem5() != 5) E(2);
  SUCCESS;
}
