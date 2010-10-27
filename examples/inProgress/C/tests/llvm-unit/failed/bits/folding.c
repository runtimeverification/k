//===--- folding.c --- Test Cases for Bit Accurate Types ------------------===////
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is used to test constant folding optimization.
//
//===----------------------------------------------------------------------===//


#include <stdio.h>


typedef int __attribute__ ((bitwidth(7))) int7;
typedef unsigned int __attribute__ ((bitwidth(7))) uint7;
typedef int __attribute__ ((bitwidth(15))) int15;

const int7 myConst = 1;
const int15 myConst2 = 0x7fff;

int main()
{
  int7 x;
  int7 y;
  int15 z;
  uint7 u;
    
  x = myConst << 3; // constant 8
  y = x + myConst;  // constant 9
  if(y -x != 1)
    printf("error1: x = %d, y = %d\n", x, y);

  x = myConst << 7; // constant 0
  if(y -x != 9)
    printf("error2: x = %d, y = %d\n", x, y);

  z = (int15) y;
  z &= myConst2;
  if(z != 0x9)
    printf("error3: x = %d, y = %d\n", x, y);

  u = 0x7f;
  u = u + (uint7)myConst;
  if(u != 0)
    printf("error4: x = %d, y = %d\n", x, y);
    
  return 0;
}
