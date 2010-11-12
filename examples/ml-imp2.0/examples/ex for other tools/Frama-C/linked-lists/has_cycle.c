
#include "list.h"

/*@ type Has_cycle_variant */

/*@ logic Has_cycle_variant has_cycle_variant(list l, list l1, list l2)
  reads l->tl */

/*@ requires
  @   finite(l)
  @ ensures 
  @   \result <=> cyclic(l) 
  @*/
int cyclic(list l) {
  list l1 = l;
  list l2;
  if (!l1) return 0;
  l2 = l1->tl;
  /*@ invariant (\exists plist pl1; lpath(l,pl1,l1)) &&
    @           (\exists plist pl12; lpath(l1,pl12,l2) && pl12!=nil())
    @ variant has_cycle_variant(l,l1,l2) for has_cycle_order
    @*/
  while (l1 != l2) {
    if (!l1 || !l2 || !l2->tl) return 0;
    l1 = l1->tl;
    l2 = l2->tl->tl;
  }
  return 1;
}

