#include "testharness.h"


/* What's going wrong here?  CIL's printing routines try to eliminate
   some trivial gotos.  In this test program, the "goto successor"
   statement is useless and therefore doesn't get printed out.
   However, the "successor:" label is left behind.  This yields a
   warning about a label being defined but not used. */


int branch(int selector)
{
  if (selector)
    return 1;
  else
    goto successor;

 successor:
  return 0;
}


int main()
{
  branch(0);
  SUCCESS;
}
