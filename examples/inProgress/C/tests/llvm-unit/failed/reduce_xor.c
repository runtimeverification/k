#include "bits.h"
#include <stdio.h>

int test_reduce_xor47(uint47 x)
{
  unsigned result = reduce(xor, x) != 0;
  printf("reduce_xor47(x) = %d\n", result);
  return result;
}  

int test_reduce_xor68(uint68 x)
{
  unsigned result = reduce(xor, x) != 0;
  printf("reduce_xor68(x) = %d\n", result);
  return result;
}  

int test_reduce_xor250(uint250 x)
{
  unsigned result = reduce(xor, x) != 0;
  printf("reduce_xor250(x) = %d\n", result);
  return result;
}  

int main(int argc, char** argv) {
  uint250 x = 0xF0F0F0F0F0F0F0F0ULL;
  int result = 0;
  int i;
  srand(128);
  for (i = 0; i < 16; ++i) {
    x *= rand();
    printf("x = 0b0");
    printBits(x);
    printf("\n");
    result = 
      test_reduce_xor47(x)  + test_reduce_xor68(x) +
      test_reduce_xor250(x);
    printf("Xor reductions of x = %d\n", result);
  }
  return 0;
}
