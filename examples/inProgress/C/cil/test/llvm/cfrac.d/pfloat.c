/*
 *	High Precision Math Library Supplement for floating point routines
 */
#include <stdio.h>
#include <math.h>
#include "pdefs.h"
#include "pcvt.h"
#include "precision.h"

extern precision palloc();

/*
 * double to precision
 */
precision dtop(f)
   register double f;
{
   register digitPtr	 uPtr;
   register precision    u;

   u = palloc(DOUBLESIZE);		/* pretty big */
   if (u == pUndef) return u;

   if (f < 0.0) {
      f = -f;
      u->sign = true;
   } else {
      u->sign = false;
   }
   uPtr	      = u->value;
   do {
      *uPtr++ = fmod(f, (double) BASE);
      f	      = floor(f / (double) BASE);
   } while (f != 0.0);

   u->size = (uPtr - u->value);

   return presult(u);
}

/*
 *  precision to double (no overflow check)
 */
double ptod(u)
   precision	  u;
{
   register digitPtr uPtr;
   register double   f;

   (void) pparm(u);
   uPtr = u->value + u->size;
   f    = 0.0;
   do {
      f = f * (double) BASE + (double) *--uPtr;
   } while (uPtr > u->value);

   if (u->sign) f = -f;

   pdestroy(u);
   return f;
}
