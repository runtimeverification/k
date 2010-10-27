#include "bits.h"
#include <stdio.h>

int main(int argc, char** argv) {
  uint68 x = 0xF0F0F0F0F0F0F0F0ULL;
  uint60 y = 0x0F0F0F0F0F0F0F0FULL;
  uint68 z = part_set(x, y, 0, (bitwidthof(y)-1)); 
  uint68 z2= part_set(x, y, (bitwidthof(y)-1), 0); 
  printf("x = ");
  printBits(x);
  printf("\ny = ");
  printBits(y);
  printf("\npart_set(x, y, 0, 59) = ");
  printBits(z);
  printf("\npart_set(x, y, 59, 0) = ");
  printBits(z2);
  printf("\n");
  return (int) z;
}
