#include "pdefs.h"
#include "precision.h"

/*
 * Convert a precision to a given base (the sign is ignored)
 *
 * Input:
 *    u        - the number to convert
 *    dest     - Where to put the ASCII representation radix
 *               WARNING! Not '\0' terminated, this is an exact image
 *    size     - the number of digits of dest.  
 *               (alphabet[0] padded on left)
 *               if size is too small, truncation occurs on left
 *    alphabet - A mapping from each radix digit to it's character digit
 *               (note: '\0' is perfectly OK as a digit)
 *    radix    - The size of the alphabet, and the conversion radix
 *               2 <= radix < 256.
 * 
 * Returns:
 *    -1 if invalid radix
 *    0  if successful
 *    >0 the number didn't fit
 */
int ptob(u, dest, size, alphabet, radix)
   precision u;			/* the number to convert */
   char *dest;			/* where to place the converted ascii */
   unsigned int size;		/* the size of the result in characters */
   char *alphabet;		/* the character set forming the radix */
   register unsigned int radix;	/* the size of the character set */
{
   register accumulator	 temp;
   register unsigned int i;
   register char *chp;
   unsigned int lgclump;
   int res = 0;

   precision	 r = pUndef, v = pUndef, pbase = pUndef;

   if (radix > 256 || radix < 2) return -1;
   if (size == 0) return 1;

   (void) pparm(u);
   temp = radix;
   i = 1;
   while  (temp * radix > temp) {
      temp *= radix;
      i++;
   }
   lgclump = i;

   pset(&v, pabs(u));
   pset(&pbase, utop(temp));	/* assumes accumulator and int are the same! */

   chp = dest + size;
   do {
      pdivmod(v, pbase, &v, &r);
      temp = ptou(r);		/* assumes accumulator and int are the same! */
      i = lgclump;
      do {
	 *--chp = alphabet[temp % radix];	       /* remainder */
	 temp = temp / radix;
	 if (chp == dest) goto bail;
      } while (--i > 0);
   } while pnez(v);

   if (chp > dest) do {
      *--chp = *alphabet;
   } while (chp > dest);

bail:
   if (pnez(v) || temp != 0) {			/* check for overflow */
      res = 1;
   }

   pdestroy(pbase);
   pdestroy(v);
   pdestroy(r);

   pdestroy(u);
   return res;
}
