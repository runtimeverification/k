#include "testharness.h"

int main()
{
  int a;
  int b __attribute__((myattribute(a == a)));
  b = 5;
  // our remove-temps code will remove "a", even though GCC thinks it is
  // necessary

  // GN: This is because the "a" in the attribute is not a reference to the
  // variable, but just an indentifier !
  SUCCESS; 
} 
