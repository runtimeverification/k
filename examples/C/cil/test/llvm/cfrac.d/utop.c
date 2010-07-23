#include "pdefs.h"
#include "pcvt.h"
#include "precision.h"

/*
 * Unsigned to Precision
 */
precision utop(i)
   register unsigned int i;
{
   register digitPtr  uPtr;
   register precision u = palloc(INTSIZE);

   if (u == pUndef) return pUndef;

   u->sign    = false;
   uPtr	      = u->value;
   do {
      *uPtr++ = modBase(i);
      i	      = divBase(i);
   } while (i != 0);

   u->size = (uPtr - u->value);
   return presult(u);
}
