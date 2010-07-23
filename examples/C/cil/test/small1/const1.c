#include "testharness.h"

unsigned long long x1 = 0xff00000000000000ULL;

int main() {
  
  // We'll use shift left to test for sign
  if((2147483647 /* 2^31 - 1 */ >> 31) != 0) E(1); // Should be signed

  if(((2147483647 + 1) >> 31) != -1) E(2); // Should be signed int

  // Should be signed long long, but both GCC and MSVC treat it as unsigned int
  if((2147483648 /* 2^31 */ >> 31) != 1) E(3);  


  if(((2147483647U + 1) >> 31) != 1) E(4); // Should be unsigned signed int


  if(x1 >> 56 != 255) E(5);

  // now see if constant folding misbehaves
  if(0xff00000000000000ULL >> 56 != 255) E(6);

  
  SUCCESS;
}

