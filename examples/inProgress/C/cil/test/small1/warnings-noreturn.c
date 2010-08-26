#include "testharness.h"


void croak() __attribute__((noreturn));
void die() __attribute__((noreturn));


void terminate(int) __attribute__((noreturn));

void terminate(int frog)
{
  if (frog)
    croak();
  else
    die();
}


int main()
{
  SUCCESS;
}
