#include "pdefs.h"
#include "pcvt.h"
#include "precision.h"

/*
 * Long to Precision
 */
precision ltop(l)
   register long l;
{
   register digitPtr  uPtr;
   register precision u = palloc(LONGSIZE);

   if (u == pUndef) return u;

   if (u->sign = (l < 0L)) l = -l;
   uPtr	      = u->value;
   do {
      *uPtr++ = modBase(l);
      l	      = divBase(l);
   } while (l != 0);

   u->size = (uPtr - u->value);			/* normalize */
   return presult(u);
}
