//===--- union2.c --- Test Cases for Bit Accurate Types -------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a test for union type. By assigning values to different
// fields, we can check whether the assignment is correctly performed.
//
// Note: In the current implementation, a 9-bit data will also occupy
// 2 bytes. So for this example, storing value to the 9-bit field will
// change the two bytes of the memory.
//
//===----------------------------------------------------------------------===//


#include <stdio.h>

typedef int __attribute__ ((bitwidth(9))) int9;
typedef int __attribute__ ((bitwidth(31))) int31;
typedef union {short i; int9 i9; int31 i31;} myUnion;
typedef struct myStruct {int9* ptr; short i;} myStruct;

myStruct test(myUnion *u)
{
  myStruct x;
  int9* ptr;
  
  u->i31 = -1;
  u->i = 0x0;
  ptr = &(u->i9);
  *ptr= -1;

  x.ptr = ptr;
  x.i = u->i;

  return x;   
}

static myUnion uu;

int main()
{
  myStruct s = test(&uu);
  printf("uu.i  = %hd\n", uu.i);
  printf("uu.i9 = %d\n", (int)uu.i9);
  printf("uu.i31= %d\n", uu.i31);
 
  if(s.i == 0x0)
    printf("error: s.i=%x\n", s.i);
  return 0;
}
