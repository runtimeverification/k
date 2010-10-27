//===--- bit_concat.c --- Test The bit_concat builtin --------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This test case tests the __builtin_part_select builtin function llvm-gcc.
// bit_select selects one bit out of a larger 
//
//===----------------------------------------------------------------------===//

#include <stdio.h>
#include <stdlib.h>
#include "bits.h"


int main(int argc, char** argv)
{
  uint169 X = 0;
  uint69 Y = 0;
  uint256 Z = 0;
  int i, j;
  int count = (argc > 1 ? atoi(argv[1]) % 65 : 64);

  srand(count);

  printf("Attempting %d bit_concat operations\n", count);
  for (i = 0; i < count; i++) {
    Y = X = 0; 
    for (j = 0; j < bitwidthof(uint169); j++) {
      X <<= 1;
      X += (rand() % 2 == 0 ? 0 : 1);
    }
    for (j = 0; j < bitwidthof(uint69); j++) {
      Y <<= 1;
      Y += (rand() % 2 == 0 ? 0 : 1);
    }
    Z = bit_concat(X, Y);
    printf("bit_concat(");
    printBits(X);
    printf(",");
    printBits(Y);
    printf(") = ");
    printBits(Z);
    printf("\n");
  }
  return 0;
}
