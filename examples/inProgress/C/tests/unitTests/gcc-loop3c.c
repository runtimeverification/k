// based on loop-3c.c from gcc torture tests

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>

void * a[255];

void f (m)
{
  int i;
  int sh = 0x100;
  i = m;
  do
    {
      a[sh >>= 1] = ((unsigned)i << 3)  + (char*)a;
      i += 4;
    }
  while (i < INT_MAX/2 + 1 + 4 * 4);
}

main ()
{
  a[0x10] = 0;
  a[0x08] = 0;
  f (INT_MAX/2 + INT_MAX/4 + 2);
  //printf("a[0x10]=%p\n", a[0x10]);
  //printf("a[0x08]=%p\n", a[0x08]);
  printf("a[0x10] || a[0x08] == %d\n", a[0x10] || a[0x08]);
  if (a[0x10] || a[0x08])
    abort ();
  a[0x10] = 0;
  a[0x08] = 0;
  f (INT_MAX/2 + 1);
  //printf("a[0x10]=%p\n", a[0x10]);
  //printf("a[0x08]=%p\n", a[0x08]);
  printf("a[0x10] || a[0x08] == %d\n", a[0x10] || a[0x08]);
  if (! a[0x10] || a[0x08])
    abort ();
  exit (0);
}
