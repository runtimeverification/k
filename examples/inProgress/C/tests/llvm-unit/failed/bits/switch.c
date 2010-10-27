//===--- switch.c --- Test Cases for Bit Accurate Types -------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a test for switch statement. The switch value is a
// non-regular bitwidth. test(int3 c) function return the value of the
// argument c. 
//
//===----------------------------------------------------------------------===//


#include <stdio.h>

typedef unsigned int __attribute__ ((bitwidth(7))) int7;
typedef unsigned int __attribute__ ((bitwidth(3))) int3;

const int7 zero = (int7)(1 << 8); // constant 0;
static int3 seven = (int3)0xf; // constant 7;

int3  test(int3 c)
{
    
  switch(c){
  case 0: return seven >> 3;
  case 1: return seven >>2;
  case 2: return (seven >> 1) & 2;
  case 3: return (seven >> 1);
  case 4: return seven & 4;
  case 5: return seven & 5;
  case 6: return seven & 6;
  case 7: return seven;
  default: printf("error\n"); return -1;
  }
  return 0;
}

int main()
{
  unsigned char  c;
  unsigned char i;

   
  for(i=0; i< ((unsigned char)zero) + 8; i++){
    c = (unsigned char)test((int3)i);
    if(c != i)
      printf("error: i=%hhd, c=%hhd\n", i, c);
  }
  return 0;
}
