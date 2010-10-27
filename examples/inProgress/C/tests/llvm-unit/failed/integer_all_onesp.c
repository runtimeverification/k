#include "bits.h"

int main(int argc, char **argv) {
  typedef uint256 BitType;

  BitType X = -1;

  printf("uint256 X = -1 -> ");
  printBits(X);
  printf("\n");

  return (int) X;
}
