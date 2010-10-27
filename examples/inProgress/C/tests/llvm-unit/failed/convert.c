//===--- convert.c --- Test Cases for Bit Accurate Types ------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
// This is a test for conversion between different int types.
//
//===----------------------------------------------------------------------===//

#include <stdio.h>

typedef int __attribute__ ((bitwidth(7))) int7;
typedef int __attribute__ ((bitwidth(15))) int15;
typedef int __attribute__ ((bitwidth(31))) int31;
typedef int __attribute__ ((bitwidth(8))) int8;

typedef unsigned int __attribute__ ((bitwidth(7))) uint7;
typedef unsigned int __attribute__ ((bitwidth(15))) uint15;
typedef unsigned int __attribute__ ((bitwidth(31))) uint31;
typedef unsigned int __attribute__ ((bitwidth(8))) uint8;

int main()
{
    int7 i7;
    int15 i15;
    int31 i31;
    int8 i8;

    uint7 ui7;
    uint15 ui15;
    uint31 ui31;
    uint8 ui8;

    i7 = 0x7f;
    i15 = (int15)i7;
    i31 = (int31)i15;
    if(i15 != -1 || i31 != -1)
      printf("error: i15=%d, i31 = %d\n", i15, i31);

    ui7 = 0x7f;
    ui15 = (uint15)ui7;
    ui31 = (uint31)ui15;
    if(ui15 != 0x7f || ui31 != 0x7f)
      printf("error: ui15=%u, ui31 = %u\n", ui15, ui31);

    i31 = -1;
    i8 = (int8) i31;
    if(i8 != -1)
      printf("error: i8=%d\n", i8);

    i31 = 0xff;
    i7 = (int7) i31;
    printf("i7=%d\n", i7);

    ui31 = 0x1ff;
    ui8 = (uint8) ui31;
    printf("ui8=%u\n", ui8);

    i8 = (int8) ui8;
    printf("i8=%d\n", i8);

    ui7 = (uint7) i7;
    printf("ui7=%u\n", ui7);
    
    return 0;
} 
