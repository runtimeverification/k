#include "pdefs.h"
#include "precision.h"

/*
 * Compare to zero (normalization not assumed)
 *
 * Returns same as pcmp(u, 0);
 */
int pcmpz(u)
   register precision u;
{
   register digitPtr uPtr;
   register int i;

   (void) pparm(u);
   i = 0;
   uPtr = u->value;
   do {
      if (*uPtr++ != 0) {
	 if (u->sign) i = -1; else i = 1;
	 break;
      }
   } while (uPtr < u->value + u->size);

   pdestroy(u);
   return i;
}

/*
 *  Compare u to v. 
 *
 *  Return:  < 0 if u < v
 *	     = 0 if u = v
 *	     > 0 if u > v
 *
 * This routine is the one that assumes results are normalized!
 *    - no leading 0's
 *    - no negative 0
 */
int pcmp(u, v)
   precision u, v;
{
   register digitPtr uPtr, vPtr;
   register int	     i;			/* should be bigger than posit */

   (void) pparm(u);
   (void) pparm(v);
   if (u->sign != v->sign) {
      if (u->sign) i = -1; else i = 1;
   } else {
      i = u->size - v->size;
      if (i == 0) {
	 uPtr = u->value + u->size; 
	 vPtr = v->value + v->size;
	 do {
	    if (*--uPtr != *--vPtr) break;
	 } while (vPtr > v->value);
	 if (*uPtr > *vPtr) i = 1;
	 else if (*uPtr < *vPtr) i = -1;
      }

      if (u->sign) i = -i;
   }

   pdestroy(u);
   pdestroy(v);
   return i;
}
