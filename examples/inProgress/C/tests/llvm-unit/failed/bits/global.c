//===--- global.c --- Test Cases for Bit Accurate Types -------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is used to test global arrays.
//
//===----------------------------------------------------------------------===//


#include <stdio.h>


typedef int __attribute__ ((bitwidth(7))) int7;
typedef int __attribute__ ((bitwidth(14))) int14;

int7 array[4] = {127, -1, 100, -28};
int14 array2[4][4];

void test()
{
  int i = 0;
  int j = 0;
  for(i=0; i<4; ++i)
    for(j=0; j<4; ++j){
      array2[i][j] = array[i] *  array[j];
      if(array2[i][j] <= 0)
        printf("error: i=%d, j=%d, result = %d\n", i, j, array2[i][j]);
    }
}

int main()
{
  int7 a = 127;
  int7 b = 100;
  printf("a=%d b=%d a*a=%d\n",a, b, a*a);
  test();
  return 0;
}
