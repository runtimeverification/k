/* 
 * This file is used to the C calling conventions with signless
 * LLVM. Integer arguments in this convention are promoted to at
 * least a 32-bit size. Consequently signed values must be 
 * sign extended and unsigned values must be zero extended to
 * at least a 32-bit integer type. 
 */

#include <stdio.h>
#include <stdlib.h>

int Y = 0;

int ubyteArg( unsigned char X) {
  return X + 2 + Y;
}

int sbyteArg( signed char X ) {
  return X + 3 + Y;
}

int ushortArg( unsigned short X ) {
  return X + 4 + Y;
}

int sshortArg( signed short X) {
  return X + 5 + Y;
}

int F1, F2, F3, F4;

int main(int argc, char**argv) {
  int TestVal;
  short sh;
  unsigned short ush;

  if (argc < 2) {
    printf("Program requires integer parameter");
    exit (1);
  }

  F1 = (int)(void*)ubyteArg;
  F2 = (int)(void*)sbyteArg;
  F3 = (int)(void*)ushortArg;
  F4 = (int)(void*)sshortArg;

  TestVal = atoi(argv[1]);
  sh = (short)-1;
  ush = (unsigned short) -1;

  printf("%d %hd %hu\n", TestVal, sh, ush);

  return 0;
}
