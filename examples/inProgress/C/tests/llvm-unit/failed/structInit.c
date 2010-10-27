//===--- structInit.c --- Test Cases for Bit Accurate Types ---------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a test for struct data structure with initialization.
//
//===----------------------------------------------------------------------===//


#include <stdio.h>

typedef int __attribute__ ((bitwidth(31))) int31;
typedef int __attribute__ ((bitwidth(24))) int24;

typedef struct Connection_Type {
   int24   to;
   char    type[10];
   int31   length;
} Connection;

Connection link[3]
= { {1, "link1", 10},
    {2, "link2", 20},
    {3, "link3", 30} };


int main()
{
  int24 l;
  for(l=0; l<3; l++)
    printf("%d, %s, %d\n", link[l].to, link[l].type, link[l].length);

  return 0;
}
