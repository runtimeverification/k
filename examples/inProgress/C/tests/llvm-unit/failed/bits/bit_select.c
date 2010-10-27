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
const BitType X = 0xAAAAAAAAAAAAAAAAULL;
#else
typedef uint47 BitType;
const BitType X = 0xAAAAAAAAAAAAULL;
#endif

int main(int argc, char** argv)
{

#ifdef ENABLE_LARGE_INTEGERS
  BitType Y = X * X;
#else
  BitType Y = X;
#endif

  BitType i;

  printBits(Y);

  printf("\n");
  return 0;
}
