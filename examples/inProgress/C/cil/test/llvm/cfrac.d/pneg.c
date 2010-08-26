#include "pdefs.h"	/* private include file */
#include "precision.h"	/* public include file for forward refs */
#include <string.h>

/*
 * negation
 */
precision pneg(u)
   register precision u;
{
   precision w;

   (void) pparm(u);
   w = palloc(u->size);
   if (w == pUndef) return w;

   w->sign = u->sign;
   if (pnez(u)) {		/* don't create a negative 0 */
      w->sign = !w->sign;
   }
   (void) memcpy(w->value, u->value, u->size * sizeof(digit));

   pdestroy(u);
   return presult(w);
}
