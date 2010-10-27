//===--- bitbit.c --- Test Cases for Bit Accurate Types -------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a general test for bit operations.
//
//===----------------------------------------------------------------------===//

#include "bits.h"
#include <stdio.h>


int my_test()
{
  int21 x = 0x1fffff;
  int21 y = 0x0fffff;
  int21 result;
  int i_result;
  result = ~x;
  i_result = result;
  printf("i_result = %x\n", i_result);
  result = x ^ y;
  i_result = result;
  printf("i_result = %x\n", i_result);
  result = x & y;
  if (result == y) 
    printf("ok\n");
  else 
    printf("fail\n");
  
  result = x | y;
  if (result == x) 
    printf("ok\n");
  else 
    printf("fail\n");
  
  result = x;
  result &= y;
  if (result == y)
    printf("ok\n");
  else 
    printf("fail\n");
  
  result = x;
  result |= y;
  if (result == x)
    printf("ok\n");
  else 
    printf("fail\n");
  
  result = x >> 20;
  i_result = result;
  printf("i_result = %x\n", i_result);
  {
    result = y << 1;
    result += 1;
    if (result != x)
      printf("fail\n");
    else 
      printf("ok\n");
    
    result = y;
    result <<= 1;
    ++result;
    
    if (result != x)
      printf("fail\n");
    else 
      printf("ok\n");
    
  }
  return 0;
  
}

int main()
{
  my_test();
  return 0;
}

