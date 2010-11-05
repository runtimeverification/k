#include "testharness.h"


//
//Test scoping of formal names
//

double renamed;

void bar(typeof(renamed) x, //"renamed" refers to the global, with type double
         int renamed,
         typeof(renamed) z) //"renamed" refers to the second formal
{
  if (sizeof(x) != sizeof(double)) E(2);
  if (sizeof(z) != sizeof(int)) E(3);
  if (x + renamed != z) E(4);
}

int main(void)
{
  bar(1.0, 2, 3);
  SUCCESS;
}
