//===--- struct1.c --- Test Cases for Bit Accurate Types ------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a test for struct data structure. If the data layout for
// non-regular bitwidth data is not correct, it may change the value of 
// another field.
//
//===----------------------------------------------------------------------===//


#include <stdio.h>

typedef int __attribute__ ((bitwidth(33))) int33;

struct foo A;
struct foo {
  int33 x;
  double D;
};

int main()
{
  A.D = -3.141593;
  A.x = -1;
  printf("%f\n", A.D);
    
  return 0;
}
