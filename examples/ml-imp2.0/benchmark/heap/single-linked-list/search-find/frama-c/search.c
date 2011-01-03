
#include "list.h"

/*@ requires is_list(l)
  @ ensures \result != \null => \result->hd == v
  @*/
list search(list l, int v) {
  list p = l;
  /*@ invariant is_list(p)
    (* variant length(p) for length_order *) */
  while (p != NULL && p->hd != v) p = p->tl;
  return p;
}
