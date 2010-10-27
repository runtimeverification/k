#include "bits.h"

int main(int argc, char**argv) {
      int54 X;
      int169 Y;
      uint250 Z = 0;
      int250 K;
      uint250 U = 0;

      X = Y = Z = K = -1;
      U = -1;
      printf("int54 X = ");
      printBits(X);
      printf("\nint169 Y = ");
      printBits(Y);
      printf("\nuint250 Z = ");
      printBits(Z);
      printf("\nuint250 U = ");
      printBits(U);
      printf("\nint250 K = ");
      printBits(K);
      printf("\n");

      K = Y = Z = X = -1;
      printf("int54 X = ");
      printBits(X);
      printf("\nint169 Y = ");
      printBits(Y);
      printf("\nuint250 Z = ");
      printBits(Z);
      printf("\nuint250 U = ");
      printBits(U);
      printf("\nint250 K = ");
      printBits(K);
      printf("\n");

      X = Y = Z = K = U = -1;
      printf("int54 X = ");
      printBits(X);
      printf("\nint169 Y = ");
      printBits(Y);
      printf("\nuint250 Z = ");
      printBits(Z);
      printf("\nuint250 U = ");
      printBits(U);
      printf("\nint250 K = ");
      printBits(K);
      printf("\n");

      return X;
}
