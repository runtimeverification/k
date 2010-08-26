#include <string.h>
#include "pdefs.h"
#include "pcvt.h"
#include "precision.h"

/*
 * Return the character string decimal value of a Precision
 */
#if (BASE > 10)
#define CONDIGIT(d)	((d) < 10 ? (d) + '0' : (d) + 'a'-10)
#else
#define CONDIGIT(d)	((d) + '0')
#endif

char *ptoa(u)
   precision u;
{
   register accumulator	 temp;
   register char *dPtr;
   char		 *d;
   int		 i = 0; 
   unsigned int	 consize;
   precision	 r, v, pbase;
   register int	 j;

   (void) pparm(u);
   r	 = pUndef;
   v	 = pUndef;
   pbase = pUndef;

   consize = (unsigned int) u->size;
   if (consize > MAXINT / aDigits) {
      consize = (consize / pDigits) * aDigits;
   } else {
      consize = (consize * aDigits) / pDigits;
   }

   consize += aDigitLog + 2;	       /* leading 0's, sign, & '\0' */
   d = (char *) allocate((unsigned int) consize);
   if (d == (char *) 0) return d;

   pset(&v, pabs(u));
   pset(&pbase, utop(aDigit));

   dPtr = d + consize;
   *--dPtr = '\0';			   /* null terminate string */
   i = u->sign;					       /* save sign */
   do {
      pdivmod(v, pbase, &v, &r);
      temp = ptou(r);		/* Assumes unsigned and accumulator same! */
      j = aDigitLog;
      do {
	 *--dPtr = CONDIGIT(temp % aBase);	       /* remainder */
	 temp = temp / aBase;
      } while (--j > 0);
   } while (pnez(v));

   while (*dPtr == '0') dPtr++;		     /* toss leading zero's */
   if (*dPtr == '\0') --dPtr;		   /* but don't waste zero! */
   if (i) *--dPtr = '-';
   if (dPtr > d) {	     /* ASSUME copied from lower to higher! */
      (void) memmove(d, dPtr, consize - (dPtr - d));
   }

   pdestroy(pbase);
   pdestroy(v);
   pdestroy(r);

   pdestroy(u);
   return d;
}
