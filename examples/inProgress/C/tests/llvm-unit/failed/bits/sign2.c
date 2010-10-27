//===--- sign.c --- Test Cases for Bit Accurate Types --------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is another test for arithmetic operations with signed and
// unsigned operands.
//
//===----------------------------------------------------------------------===//
#include <stdio.h>

typedef int __attribute__ ((bitwidth(24))) int24;
typedef unsigned int __attribute__ ((bitwidth(24))) uint24;


int
main ( int argc, char** argv)
{
  int num, r;
  int24 x, y, z;
  uint24 ux, uy, uz;

  r = rand();
  ux = r;
  x = r;
  printf("rand() = %d\n", r);
  
  printf("ux = %u, x = %d\n", ux, x);

  z = x / 4321;
  uz = ux / (unsigned)4321;
  printf("uz = %u, z = %d\n", uz, z);

  y = x + 0x800000;
  uy = x + 0x800000u;
  printf("uy = %u, y = %d\n", uy, y);

  z = y / x ;
  uz = uy / ux ;
  printf("ux = %u, x = %d\n", uz, z);

  z = x / y ;
  uz = ux / uy ;
  printf("ux = %u, x = %d\n", uz, z);
  
  return 0;
}
