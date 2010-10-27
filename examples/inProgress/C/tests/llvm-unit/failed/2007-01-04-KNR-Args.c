#include <stdio.h>

p1 (c, f1, s, d1, i, f2, l, d2)
char c; float f1; short s; double d1; int i; float f2; long l; double d2;
{
  printf("%c %f %d %f %d %f %d %f\n", c, f1, s, d1,i, f2, l, d2);
}

void p2 (char c, float f1, short s, double d1, int i, float f2, long l, double d2)
{
  printf("%c %f %d %f %d %f %d %f\n", c, f1, s, d1,i, f2, l, d2);
}

int main(int argc, const char *argv[]) {
  p1 ('a', 4.0, 1, 5.0, 2, 4.0, 3, 5.0);
  p2 ('a', 4.0, 1, 5.0, 2, 4.0, 3, 5.0);
  return 0;
}

