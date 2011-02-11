#include "list.h"

/*@ requires \exists plist l; llist(c,l) && list_length(l) >= 2
  @ ensures \forall plist l; \forall list c1; \forall list c2;
  @   \old(llist(c, cons(c1,cons(c2,l)))) => 
  @     llist(\result, cons(c2,cons(c1,l)))
  @*/
list swap(list c) {
  list p;
  if (c != NULL) {
    p = c;
    c = c -> tl;
    p -> tl = c -> tl;
    c -> tl = p;
  }
  return c;
}

