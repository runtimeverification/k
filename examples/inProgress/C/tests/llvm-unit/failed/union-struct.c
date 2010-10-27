//===--- union-struct.c --- Test Cases for Bit Accurate Types -------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a test for struct with union inside. The purpose is to see
// whether the size of the structure is correct.
//
//===----------------------------------------------------------------------===//


#include <stdio.h>

typedef int __attribute__ ((bitwidth(31))) int31;

struct Blend_Map_Entry {
  union {
    float Colour[5];
    double Point_Slope[2];
    int31  weight[5];
  } Vals;
};



int main()
{
  if( sizeof(struct Blend_Map_Entry) != 5 * sizeof(int) )
    printf("error: %d\n", sizeof(struct Blend_Map_Entry));
  return 0;
}
