#include "precision.h"

/*
 * Raise to precision power mod m
 */
precision ppowmod(u, v, m)
   precision 	u, v, m;
{
   precision j = pUndef, i = pUndef, n = pUndef;

   (void) pparm(m);
   pset(&i,   pparm(u));
   pset(&n,   pparm(v));
   pset(&j,   pone);

   do {
      if (podd(n)) {
	 pset(&j, pmod(pmul(i, j), m));
      }
      pset(&n, phalf(n));
      if (peqz(n)) break;
      pset(&i, pmod(pmul(i, i), m));
   } while (1);

   pdestroy(i); pdestroy(n);
   pdestroy(u); pdestroy(v); pdestroy(m);
   return presult(j);
}
