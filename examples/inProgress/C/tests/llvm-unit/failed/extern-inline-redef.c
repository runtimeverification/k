//===--- extern_inline_redef.c --- Test Cases for Bit Accurate Types ------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// this is used to test redefining inline function.  
//
//===----------------------------------------------------------------------===//


#include <stdio.h>

typedef int __attribute__ ((bitwidth(61))) int61;

extern __inline int61
  __strtol_l (int a)
{
  return 0;
}

int61
  __strtol_l (int a)
{
  return 0;
}

int main()
{
  return 0;
}
