#include "pdefs.h"
#include "pcvt.h"
#include "precision.h"

/*
 *  Precision to unsigned 
 */
unsigned int ptou(u)
   precision u;
{
   register digitPtr uPtr;
   register accumulator temp;

   (void) pparm(u);
   if (u->sign) {
      temp = (unsigned int) errorp(PDOMAIN, "ptou", "negative argument");
   } else {
      uPtr = u->value + u->size;
      temp = 0;
      do {
	 if (temp > divBase(MAXUNSIGNED - *--uPtr)) {
	    temp = (unsigned int) errorp(POVERFLOW, "ptou", "overflow");
	    break;
	 }
	 temp  = mulBase(temp);
	 temp += *uPtr;
      } while (uPtr > u->value);
   }
   pdestroy(u);
   return (unsigned int) temp;
}
