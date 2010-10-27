//===--- SSAtest.c --- Test Cases for Bit Accurate Types ------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Adopted the test from previous test-cases. Changed it with
// non-regular int data type.
//
//===----------------------------------------------------------------------===//


#include <stdio.h>

typedef int __attribute__ ((bitwidth(4))) int4;

int4 bar()
{
    return 0xf;
}

int4 foo()
{
  int4 a,b,c;
  b = 0;
  c = 0;
  a = b + c;
  b = bar();
  c = bar();
  printf("result = %d\n", a + b + c);
}


int main()
{
  foo();
  return 0;
}
