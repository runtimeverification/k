/*
 * Test basic conversions between short signed and unsigned values
 * with no function calls and no arithmetic.
 */
#include <stdio.h>

unsigned char getUC() { return 0x80; }

         char getC()  { return 0x80; }

int main()
{
  char            C80 = getC();
  unsigned char  UC80 = getUC();

  /* source is smaller than dest: both decide */
  unsigned short us  = (unsigned short)  C80;     /* sign-ext then zero-ext */
  unsigned short us2 = (unsigned short) UC80;     /* zero-ext only: NOP! */
           short  s  = (         short)  C80;     /* sign-ext */ 
           short  s2 = (         short) UC80;     /* zero-extend only : NOP! */
  printf("%d %d --> unsigned: us = %d, us2 = %d\n", C80, UC80, us, us2);
  printf("%d %d -->   signed:  s = %d,  s2 = %d\n", C80, UC80,  s,  s2);

  /* source is same size or larger than dest: dest decides */
  unsigned char  uc  = (unsigned char )  C80;     /* zero-ext */
  unsigned char  uc2 = (unsigned char ) UC80;     /* NOP */
           char   c  = (         char )  C80;     /* NOP */
           char   c2 = (         char ) UC80;     /* sign-extend */
  printf("%d %d --> unsigned: uc = %d, uc2 = %d\n", C80, UC80, uc, uc2);
  printf("%d %d -->   signed:  c = %d,  c2 = %d\n", C80, UC80,  c,  c2);
  return 0;
}
