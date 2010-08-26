
#include "testharness.h"


typedef struct 
{
 int b;
} str2;
typedef struct 
{
 int c;
 int d;
} str4;
typedef struct
{
   int a;
   union u
   {
      str2 m1;
      str4 m2;
   } u;
} str3;

int scrambleTheStack(int x) __attribute__((__noinline__))
{
  char junk[256];
  int i = 0;
  while (i < 256) {junk[i++] = 0xaa; }
  return junk[x];
}

//What to do with the union z.u, which has no explicit initializer?
//ISO C says to initialize only the first field (m1, which is smaller than m2),
//but gcc initializes the whole union to zero

void test(void) __attribute__((__noinline__))
{
    str3   z = {0};
    printf ("z.u.m2.d = 0x%x\n", z.u.m2.d);
    if (z.u.m2.d != 0) E(2);
}


int main(void) 
{
  scrambleTheStack(200);
  test();
  return 0;
}
