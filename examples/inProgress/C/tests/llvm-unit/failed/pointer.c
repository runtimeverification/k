//===--- pointer.c --- Test Cases for Bit Accurate Types ------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a test for address calculation with non-regular integral type.
//
//===----------------------------------------------------------------------===//


#include <stdio.h>

typedef int __attribute__ ((bitwidth(3))) int3;
typedef int __attribute__ ((bitwidth(31))) int31;

int3 *test(int3* C)
{
  return C-1;   
}

int31 *test2(int31* I)
{
  return I-1;
}

int main()
{
  int3 i3;
  int31 i31;

  if(&i3 != (test(&i3) + 1))
    printf("error\n");
    
  if(&i31 != (test2(&i31)+1))
    printf("error2: &i31=%p, ret = %p\n", &i31, test2(&i31));

  return 0;
}
