#include "bits.h"
#include <stdio.h>

uint68 test_part_set(uint68 x, uint60 y)
{
  printf("uint68 x = ");
  printBits(x);
  printf("\n");

  printf("uint60 y = ");
  printBits(y);
  printf("\n");

  printf("part_set(x,y,0,59) = ");
  uint68 z = part_set(x, y, 0, (bitwidthof(y)-1)); 
  printBits(z);
  printf("\n");

  printf("part_set(x,y,59,0) = ");
  z = part_set(x, y, (bitwidthof(y)-1), 0); 
  printBits(z);
  printf("\n");

  printf("part_set(x,0,0,31) = ");
  z = part_set(x, 0, 0, 31);
  printBits(z);
  printf("\n");

  return z;
}

int main(int argc, char** argv) {
  uint68 A = 0xF0F0F0F0F0F0F0F0ULL;
  uint60 B = 0x0F0F0F0F0F0F0F0FULL;
  uint68 X = test_part_set(A, B);
  return 0;
}
