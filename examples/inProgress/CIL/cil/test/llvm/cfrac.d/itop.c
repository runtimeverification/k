#include "pdefs.h"
#include "pcvt.h"
#include "precision.h"

/*
 * Integer to Precision
 */
precision itop(i)
   register int i;
{
   register digitPtr  uPtr;
   register precision u = palloc(INTSIZE);

   if (u == pUndef) return u;

   if (u->sign = (i < 0)) i = -i;
   uPtr	      = u->value;
   do {
      *uPtr++ = modBase(i);
      i	      = divBase(i);
   } while (i != 0);

   u->size = (uPtr - u->value);			/* normalize */
   return presult(u);
}
