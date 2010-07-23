#include "../small1/testharness.h"
#include "../small1/testkinds.h"

#ifndef ERROR 
#define __WILD
#endif

// NUMERRORS 1
typedef struct foo Foo;
struct bar
{
  Foo * __WILD next;
};
struct foo
{
  int *base;
  unsigned int length;
  struct bar link;
};
int main()
{
  struct foo s, *sptr = &s;
  if(HAS_KIND(sptr->base, WILD_KIND)) E(1); //ERROR(1):Error 1
}
