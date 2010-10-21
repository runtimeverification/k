#include "fsl-header.h"
int var = 0;

void g ()
{
  var = 1;
}

void f ()
{
  int f2 = 0;

  if (f2 == 0)
    ;

  g ();
}

main ()
{
  f ();
  if (var != 1)
    abort ();
  exit (0);
}
