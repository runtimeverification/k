#include "testharness.h"

int main()
{
  double f1 = 5.e-1 ;           // KAI CC emits code like this
  double f2 = 5.00000e-1 ;      // this is normal

  if (f1 != f2) {
    E(1);
  } 
  SUCCESS;
}
