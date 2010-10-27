//===--- bitlogic.c --- Test Cases for Bit Accurate Types -----------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a general test for logical operations.
//
//===----------------------------------------------------------------------===//

#include "bits.h"
#include <stdio.h>


int my_test()
{
  uint1 x = 0x1;
  uint1 y;
  int9 z = 0x1ff;
  uint9 uz = 0x1ff;
  uint9 temp;
  y = x;
  y -= 1;
  if (!y)
    printf("ok\n");
  else 
    printf("fail\n");
  
  if (y > x)
    printf("fail\n");
  else 
    printf("ok\n");
  
  if (z != uz)
    printf("ok\n");
  else 
    printf("fail\n");
  
  temp = z;
  if (temp <= uz)
    printf("ok\n");
  else 
    printf("fail\n");
  
  return 0;

}

int main()
{
  my_test();
  return 0;
}

