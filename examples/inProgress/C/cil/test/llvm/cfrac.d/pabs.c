#include "pdefs.h"	/* private include file */
#include "precision.h"	/* public include file for forward refs */
#include <string.h>

/*
 * absolute value
 */
precision pabs(u)
   register precision u;
{
   register precision w;

   (void) pparm(u);
   w = palloc(u->size);
   if (w == pUndef) return w;

   w->sign = false;
   (void) memcpy(w->value, u->value, u->size * sizeof(digit));

   pdestroy(u);
   return presult(w);
}
