

/* in-place list reversal */

#include "list.h"

/*@ requires is_list(p0)
  @ ensures \forall plist l0; \old(llist(p0, l0)) => llist(\result, rev(l0))
  @*/
list rev(list p0) {
  list r = p0;
  list p = NULL;
  /*@ invariant 
        \exists plist lp; \exists plist lr;
          llist(p, lp) && llist(r, lr) && disjoint(lp, lr) &&
          \forall plist l; 
            \old(llist(p0, l)) => app(rev(lr), lp) == rev(l)
    @ variant length(r) for length_order */
  while (r != NULL) {
    list q = r;
    r = r->tl;
    q->tl = p;
    p = q;
  }
  return p;
}

/* test */

#if 0
#include <stdio.h>

void print(list l) {
  if (l == NULL) 
    printf("NULL\n");
  else {
    printf("%d :: ", l->hd);
    print(l->tl);
  }
}

int main() {
  /* 1::2::3::NULL */
  struct struct_list l[3];
  list r;
  l[0].hd = 1;
  l[0].tl = &l[1];
  l[1].hd = 2;
  l[1].tl = &l[2];
  l[2].hd = 3;
  l[2].tl = NULL;
  print(l);
  r = rev(l);
  print(r);
}
#endif
