
#include "bits.h"

int main()
{
  int128 X = 0xde7ed959bcfdb200ULL;
  int X0 = 0xde7ed959bcfdb200ULL;
  
  int8 X1 = X0; // Truncate to 0x00

  uint19 r, r0, r1;
  
  printf("\n X=");
  printBits(X);

  r0 = part_select(X0, 0, 18);
  r = part_select(X, 0, 18);
  r1 = part_select(X1, 0, 7);

  printf("\n r0 =");
  printBits(r0);

  printf("\n r  ="); // Wrong!
  printBits(r);

  printf("\n r1 ="); // Zero
  printBits(r1);
  printf("\n");

  return r;
}
