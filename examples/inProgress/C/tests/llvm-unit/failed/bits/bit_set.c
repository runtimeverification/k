//===--- bit_select.c --- Test The bit_select builtin ---------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This test case tests the __builtin_bit_select builtin function llvm-gcc.
// bit_select selects one bit out of a larger 
//
//===----------------------------------------------------------------------===//

#include <stdio.h>
#include "bits.h"

#ifdef ENABLE_LARGE_INTEGERS
typedef uint250 BitType;
BitType X = 0;
#else
typedef uint47 BitType;
BitType X = 0;
#endif

int main(int argc, char** argv)
{

  int i;

  printBits(X);
  printf("\n");
  for (i = bitwidthof(BitType); i > 0; --i) {
    X = bit_set(X, 1, i-1);
    printBits(X);
    printf("\n");
  }
  return 0;
}
