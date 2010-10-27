//===--- static.c --- Test Cases for Bit Accurate Types -------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a test for static data with non-regular integral data.
//
//===----------------------------------------------------------------------===//


#include <stdio.h>

typedef int __attribute__ ((bitwidth(31))) int31;

int31 test(int31 y, int31* z)
{
  static int31 x = 0;
  *z =  x;
  x = y;
  return x;
}

int main()
{
  int31 a, b;
  a = test(1, &b);
  if(b != 0 || a != 1)
    printf("error\n");
  a = test(-1, &b);
  if(b != 1 || a != -1)
    printf("error\n");
  return 0;
    
}
