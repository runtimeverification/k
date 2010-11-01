#include "fsl-header.h"
short x1 = 17;

struct
{
  short i __attribute__ ((packed));
} t;

void f ()
{
  t.i = x1;
  if (t.i != 17)
    abort ();
}

main ()
{
  f ();
  exit (0);
}
