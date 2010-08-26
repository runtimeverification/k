// testing proper lexical interpretation of integer literals

#include <stdio.h>    // printf
#include <stdlib.h>   // exit

//Make sure that $ is allowed in identifiers:
void print$Int(char *label, int i, int shouldBe)
{
  printf("%s: decimal %d, octal 0%o, hex 0x%X, shouldBe %d (decimal)\n",
         label, i, i, i, shouldBe);
  if (i != shouldBe) {
    printf("this is wrong\n");
    exit(2);
  }
}

#define PVAL(val, should) print$Int(#val, val, should)

int main()
{
  PVAL(0, 0);
  PVAL(1, 1);
  PVAL(10, 10);     // decimal
  PVAL(010, 8);     // octal (leading "0")
  PVAL(0x10, 16);   // hexadecimal (leading "0x")
  PVAL(100, 100);
  PVAL(0100, 64);
  PVAL(0101, 65);
  PVAL(0x0101, 257);
  PVAL(1 | 64 | 512, 577);
  PVAL(01 | 0100, 65);
  PVAL(01 | 0100 | 01000, 577);
  // Now check for some overflow
  PVAL(0xFFFFFFFF, -1);
  PVAL(0x80000000 | 0x7FFFFFFFU, -1);
  return 0;
}
