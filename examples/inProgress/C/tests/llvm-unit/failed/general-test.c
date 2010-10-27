//===--- general-test.c - General Bit Accurate Type Test ------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
// details.
//
//===----------------------------------------------------------------------===//
//
// This test just tries out a few bitwidth attribute constructs and 
//
//===----------------------------------------------------------------------===//

#include <stdio.h>
#include <stdlib.h>

#define ATTR_BITS(N) __attribute__((bitwidth(N))) 

typedef unsigned char ATTR_BITS( 4) My04BitInt;
typedef unsigned short ATTR_BITS(16) My16BitInt;
typedef unsigned int ATTR_BITS(17) My17BitInt;
typedef unsigned long long ATTR_BITS(37) My37BitInt;
typedef unsigned ATTR_BITS(63) My63BitInt;

struct MyStruct {
  struct MyStruct* next;
  My04BitInt i4Field;
  unsigned short ATTR_BITS(12) i12Field;
  unsigned ATTR_BITS(17) i17Field;
  My37BitInt i37Field;
};

struct MyStruct Data1;
struct MyStruct Data2;

struct MyStruct* getSizes( short ATTR_BITS(23) num, My37BitInt * result) {
  My17BitInt i;
  short __attribute__((bitwidth(9))) j;
  printf("sizeof(MyStruct) == %d\n", sizeof(struct MyStruct));
  printf("sizeof(My17BitInt) == %d\n", sizeof(My17BitInt));
  printf("sizeof(j) == %d\n", sizeof(j));
  *result = sizeof(My17BitInt) + sizeof(j) + sizeof(struct MyStruct);
  Data1.i4Field = num;
  Data1.i12Field = num + 1;
  Data1.i17Field = num + 2; 
  Data1.i37Field = num + 3;
  Data1.next = 0;
  Data2 = Data1;
  Data2.i4Field  *= 7;
  Data2.i12Field *= 7;
  Data2.i17Field *= 7;
  Data2.i37Field *= 7;
  Data2.next = &Data1;
  j = num * 2;
  printf("j = %d\n", j);
  printf("size sum is %d\n", (int)*result);
  return &Data2;
}

int
main ( int argc, char** argv)
{
  srand(0);
  struct MyStruct* strct = malloc(sizeof(struct MyStruct));
  int r = rand();
  int num = 0;
  int ATTR_BITS(23) val = 0;
  My37BitInt sizes = 0;
  printf("rand = %d\n", r);
  printf("argc = %d\n", argc);
  if (argc > 1)
    num = atoi(argv[1]);
  printf("num  = %d\n", num);
  val = r + argc + num;
  printf("val  = %d\n", val);
  struct MyStruct* that = getSizes(val, &sizes);
  printf("that.i4Field  = %d\n", (int)that->i4Field);
  printf("that.i12Field = %d\n", (int)that->i12Field);
  printf("that.i17Field = %d\n", (int)that->i17Field);
  printf("that.i37Field = %d\n", (int)that->i37Field);
  printf("next.i4Field  = %d\n", (int)that->next->i4Field);
  printf("next.i12Field = %d\n", (int)that->next->i12Field);
  printf("next.i17Field = %d\n", (int)that->next->i17Field);
  printf("next.i37Field = %d\n", (int)that->next->i37Field);
  return ((int)sizes) & 1;
}
