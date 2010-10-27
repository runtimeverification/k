#include <stdio.h>
#include <stdarg.h>

/* 5 bytes. */
typedef struct DWordS_struct    { int i; char c; } DWordS;

/* 12 bytes if d is 4-byte aligned; 16 bytes if d is 8-byte aligned. */
typedef struct QuadWordS_struct { int i; double d; } QuadWordS;

/* 20 bytes if d is 4-byte aligned; 28 bytes if d is 8-byte aligned
 * (assuming pointer size is 4 bytes and 8 bytes respectively). */
typedef struct LargeS_struct { int i; double d; DWordS* ptr; int j; } LargeS;

void test(char *fmt, ...) {
  va_list ap, aq;
  int d;
  char c, *s;
  DWordS dw;
  QuadWordS qw;
  LargeS ls;

  va_start(ap, fmt);

  va_copy(aq, ap);    /* test va_copy */
  va_end(aq);

  while (*fmt)
    switch(*fmt++) {
    case 's':           /* string */
      s = va_arg(ap, char *);
      printf("string %s\n", s);
      break;
    case 'i':           /* int */
      d = va_arg(ap, int);
      printf("int %d\n", d);
      break;
    case 'd':
      printf("double %f\n", va_arg(ap, double));
      break;
    case 'l':
      printf("long long %lld\n", va_arg(ap, long long));
      break;
    case 'c':           /* char */
      /* need a cast here since va_arg only
         takes fully promoted types */
      c = (char) va_arg(ap, int);
      printf("char %c\n", c);
      break;
    case 'D':
      dw = va_arg(ap, DWordS);
      printf("DWord { %d, %c }\n", dw.i, dw.c);
      break;
    case 'Q':
      qw = va_arg(ap, QuadWordS);
      printf("QuadWord { %d, %f }\n", qw.i, qw.d);
      break;
    case 'L':
      ls = va_arg(ap, LargeS);
      printf("LargeS { %d, %f, 0x%d, %d }\n", ls.i, ls.d, ls.ptr != 0, ls.j);
      break;
    }
  va_end(ap);
}

int main() {
  DWordS dw = { 18, 'a' };
  QuadWordS qw = { 19, 20.0 };
  LargeS ls = { 21, 22.0, &dw, 23 };

  test("ssiciiiiis", "abc", "def", -123, 'a', 123, 6, 7, 8, 9, "10 args done!");

  /* test promotion & 64-bit types */
  test("ddil", 1.0, 2.0f, (short)32764, 12345677823423LL);

  /* test passing structs by value to varargs */
  test("DQL", dw, qw, ls);

  return 0;
}
