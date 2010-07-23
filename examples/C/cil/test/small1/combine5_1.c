/* A test with 3 files. In the first two files we include the same .h and in 
 * the third file we copy the contents of the include */
#include "combine5.h"
#include "testharness.h"

int main() {
  printf("Address of TimeOuts=%x\n", &TimeOuts);
  return 0;
}
