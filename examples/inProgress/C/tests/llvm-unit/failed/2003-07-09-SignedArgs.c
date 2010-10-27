/*
 * Test sign extensions on short signed values passed as arguments
 * to function calls.  Include arithmetic to produce extra high bits
 * from operations that overflow.  Lots of codes do this!
 */
#include <stdio.h>
#include <stdarg.h>
#include <inttypes.h>

short getShort(char c, char c2, char c3, short s, short s2, int i);
int   getUnknown(char c, ...);

int passShort(char c, short s)
{
  char  c2 = s + c;
  char  c3 = s - c;
  short s2 = s * c;
  int    i = s * s * c * c;
  short s3 = getShort(c, c2, c3, s, s2, i);   /* args shd be sign-extended */
  return getUnknown(c, c2, c3, s, s2, s3, i); /* args shd be promoted to int */
}

int main()
{
  printf("%d\n", passShort(0x80, 0xf0f4));
  return 0;
}

short getShort(char c, char c2, char c3, short s, short s2, int i)
{
  int bc  = c  == (char) -128;
  int bc2 = c2 == (char) 116;
  int bc3 = c3 == (char) 116;
  int bs  = s  == (short) -3852;
  int bs2 = s2 == (short) -31232;
  int bi  = i  == (int) -1708916736;
  
  printf("getShort():\t%d %d %d %d %d %d\n", bc, bc2, bc3, bs, bs2, bi);
  printf("getShort():\t%d %d %d %d %d %d\n",  c,  c2,  c3,  s,  s2,  i);
  return (c + c2 + c3 + s + s2) + (short) i;
}

int getUnknown(char c, ...)
{
  char c2, c3;
  short s, s2, s3;
  int i;
  va_list ap;

  va_start(ap, c);
  c2 = (char)  va_arg(ap, int);
  c3 = (char)  va_arg(ap, int);
  s  = (short) va_arg(ap, int);
  s2 = (short) va_arg(ap, int);
  s3 = (short) va_arg(ap, int);
  i  =         va_arg(ap, int);
  va_end(ap);

  printf("getUnknown():\t%d %d %d %d %d %d %d\n", c, c2, c3, s, s2, s3, i);
  return c + c2 + c3 + s + s2 + s3 + i;
}
