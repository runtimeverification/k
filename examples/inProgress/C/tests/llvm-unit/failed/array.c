//===--- array.c --- Test Cases for Bit Accurate Types --------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a general test for array data types.
//
//===----------------------------------------------------------------------===//

#include "bits.h"
#include <stdio.h>

typedef enum bool{false=0, true=1} bool;

int my_test(){
  {
    int33 array[8];
    unsigned int i = 0;
    long long tmp;
    {
      i = 0;
      for ( ; ; ) {
        bool ssdm_tmp_1 = (i < 8);
        if (!ssdm_tmp_1) break;
        {
          array[i] = -(i + 1);
          tmp = array[i];
          printf("i=%u: %x\n", i, tmp);
        }
        ++i;
      }
    }
    int33* ptr;
    ptr = &array[7];
    *ptr = array[1] % array[0];
    tmp = *ptr;
    printf("%x\n", tmp);
    return 0;
  }
}


int main()
{
  my_test();
  return 0;
}


