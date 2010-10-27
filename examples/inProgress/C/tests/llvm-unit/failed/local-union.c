//===--- local-union.c --- Test Cases for Bit Accurate Types --------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a test for local union data type.
//
//===----------------------------------------------------------------------===//

#include <stdio.h>

typedef int __attribute__ ((bitwidth(33))) int33;

union foo { int X; int33 Y;};

double test(union foo* F)
{
  union foo { float X; int33 Y;} A;
  A.Y = 0x1ffffffffULL;
  return A.X;
}

int main()
{
  union foo F;
    
  printf("return  = %f\n", test(&F));
  return 0;
}
