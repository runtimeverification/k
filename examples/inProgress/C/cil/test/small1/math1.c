#include "testharness.h"

#include <math.h>

int main() {
  double d = HUGE_VAL;

#ifdef __USE_ISOC99
  double df = HUGE_VALF;
  double dl = HUGE_VALL;
#endif
  
  SUCCESS;
}
