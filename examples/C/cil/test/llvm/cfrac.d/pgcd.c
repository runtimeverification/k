#include "precision.h"

/*
 * Euclid's Algorithm
 *
 * Given u and v, calculated and return their greatest common divisor.
 */
precision pgcd(u, v)
   precision u, v;
{
   precision u3 = pnew(pabs(pparm(u))), v3 = pnew(pabs(pparm(v)));
   precision q  = pUndef, r  = pUndef;

   while (pnez(v3)) {
      pdivmod(u3, v3, &q, &r);
      pset(&u3, v3);
      pset(&v3, r);
   }

   pdestroy(v3);
   pdestroy(q);  pdestroy(r);  
   pdestroy(u);  pdestroy(v);
   return presult(u3);			/* result always positive */
}
