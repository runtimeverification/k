#include <stdarg.h>
#include <string.h>
#include "../small1/testharness.h"

//Test for OO and varargs.  These features are not supported,
// so this is not in the regression suite.

#ifndef CCURED
#define __RTTI
#endif

typedef struct parent {
  int  *f1;
} Parent;

#pragma ccured_extends("Schild", "Sparent")

typedef struct child {
  int  *f1;
  int  f2;
} Child;

// Expects a Child*, then a Parent*, then a Child
void vararg(int x, ...);

int main() {
  int x = 5;
  Child c = {&x, 2};
  void* __RTTI cp = &c;
  vararg(4, cp, cp, c);
  SUCCESS;
}


void vararg(int x, ...) {
  va_list marker;
  va_start(marker, x);

  Child * cp = va_arg(marker, Child*);
  if (cp->f2 != 2) E(10);

  void * __RTTI vp = va_arg(marker, void* __RTTI);
  Parent* p = vp;
  if (*(p->f1) != 5) E(11);

  Child c = va_arg(marker, Child);
  if (c.f2 != 2) E(12);

}

