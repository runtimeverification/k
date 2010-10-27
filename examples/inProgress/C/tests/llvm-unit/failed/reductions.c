#include "bits.h"
#include <stdio.h>

int test_reduce_or(uint68 x)
{
  unsigned result = reduce(or, x) != 0;
  printf("reduce(or, x) = %d\n", result);
  return result;
}

int test_reduce_nor(uint68 x)
{
  unsigned result = reduce(nor, x) != 0;
  printf("reduce(nor, x) = %d\n", result);
  return result;
}  

int test_reduce_xor(uint68 x)
{
  unsigned result = reduce(xor, x) != 0;
  printf("reduce(xor, x) = %d\n", result);
  return result;
}  

int test_reduce_nxor(uint68 x)
{
  unsigned result = reduce(nxor, x) != 0;
  printf("reduce(nxor, x) = %d\n", result);
  return result;
}  

int test_reduce_and(uint68 x)
{
  unsigned result = reduce(and, x) != 0;
  printf("reduce(and, x) = %d\n", result);
  return result;
}  

int test_reduce_nand(uint68 x)
{
  unsigned result = reduce(nand, x) != 0;
  printf("reduce(nand, x) = %d\n", result);
  return result;
}  


int main(int argc, char** argv) {
  uint68 x = 0xF0F0F0F0F0F0F0F0ULL;
  int result = 0;
  printf("x = ");
  printBits(x);
  printf("\n");
  result = 
    test_reduce_or(x)  + test_reduce_nor(x) +
    test_reduce_xor(x) + test_reduce_nxor(x) +
    test_reduce_and(x) + test_reduce_nand(x);
  printf("Sum of reductions of x = %d\n", result);
  return result;
}
