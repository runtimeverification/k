#include <ctype.h>
#include "pdefs.h"
#include "pcvt.h"
#include "precision.h"

/*
 * ascii to precision (modeled after atoi)
 *   leading whitespace skipped
 *   an optional leading '-' or '+' followed by digits '0'..'9' 
 *   leading 0's Ok
 *   stops at first unrecognized character
 *
 * Returns: pUndef if an invalid argument (pUndef or nondigit as 1st digit)
 */
precision atop(chp)
   register char *chp;
{
   precision res   = pUndef;
   precision clump = pUndef;
   int sign = 0;
   register int ch;
   register accumulator temp;
   accumulator x; 
   register int i;

   if (chp != (char *) 0) {
      while (isspace(*chp)) chp++;	/* skip whitespace */
      if (*chp == '-') {
	 sign = 1;
	 ++chp;
      } else if (*chp == '+') {
	 ++chp;
      }
      if (isdigit(ch = * (unsigned char *) chp)) {
	 pset(&res, pzero);
	 pset(&clump, utop(aDigit));
	 do {
	    i = aDigitLog-1;
	    temp = ch - '0';
	    do {
	       if (!isdigit(ch = * (unsigned char *) ++chp)) goto atoplast;
	       temp = temp * aBase + (ch - '0');
	    } while (--i > 0);
	    pset(&res, padd(pmul(res, clump), utop(temp)));
	 } while (isdigit(ch = * (unsigned char *) ++chp));
	 goto atopdone;
atoplast:
	 x = aBase;
	 while (i++ < aDigitLog-1) {
	    x *= aBase;
	 }
	 pset(&res, padd(pmul(res, utop(x)), utop(temp)));
atopdone:
	 if (sign) {
	    pset(&res, pneg(res));
	 }
      }
   }
   pdestroy(clump);
   return presult(res);
}
