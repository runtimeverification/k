#include "precision.h"

/*
 *  Square root
 */
precision psqrt(y)
   precision y;
{
   int i;
   precision x = pUndef, lastx = pUndef;

   i = pcmpz(pparm(y));
   if (i == 0) {				/* if y == 0 */
      pset(&lastx, pzero);
   } else if (i < 0) {				/* if y negative */
      pset(&x, errorp(PDOMAIN, "psqrt", "negative argument"));
   } else {
      pset(&x, y);
      do {
	 pset(&lastx, x);
	 pset(&x, phalf(padd(x, pdiv(y, x))));
      } while (plt(x, lastx));
   }

   pdestroy(x);

   pdestroy(y);
   return presult(lastx);
}
