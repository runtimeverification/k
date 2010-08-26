#include "pdefs.h"
#include "precision.h"
#include <string.h>

#ifdef ASM_16BIT
#include "asm16bit.h"
#endif

/*
 *   Subtract u from v (assumes normalized)
 */
precision psub(u, v)
#ifndef ASM_16BIT
   precision u, v;
{
   register digitPtr	HiDigit, wPtr, uPtr;
   register digitPtr 	vPtr;
#else
   register precision 	u, v;
{
   register digitPtr	wPtr, uPtr;
#endif
   precision		w;
   register accumulator temp; 
#ifndef ASM_16BIT
   register digit	noborrow;
#endif
   register int 	i;

   (void) pparm(u);
   (void) pparm(v);
   if (u->sign != v->sign) {		/* Are we actually adding? */
      w = pUndef;
      v->sign = !v->sign;		/* may generate -0 */
      pset(&w, padd(u, v));
      v->sign = !v->sign;
   } else {
      i = pcmp(u, v);
      if (u->sign) i = -i;		/* compare magnitudes only */

      if (i < 0) {
	 w = u; u = v; v = w;		/* make u the largest */
      } 

      w = palloc(u->size);	/* may produce much wasted storage */
      if (w == pUndef) return w;

      if (i < 0) w->sign = !u->sign; else w->sign = u->sign;

      uPtr     = u->value;
      wPtr     = w->value;
#ifndef ASM_16BIT
      vPtr     = v->value;
      noborrow = 1;

      HiDigit  = v->value + v->size;	      /* digits in both args */
      do {				   
	 temp	  = (BASE-1) - *vPtr++;	     /* 0 <= temp <   base   */
	 temp	 += *uPtr++;		     /* 0 <= temp < 2*base-1 */
	 temp	 += noborrow;		     /* 0 <= temp < 2*base   */
	 noborrow = divBase(temp);	       /* 0 <= noborrow <= 1 */
	 *wPtr++  = modBase(temp);
      } while (vPtr < HiDigit);

      HiDigit  = u->value + u->size;		 /* propagate borrow */
      while (uPtr < HiDigit) {
	 temp	  = (BASE-1) + *uPtr++;
	 temp	 += noborrow;		     /* 0 <= temp < 2 * base */
	 noborrow = divBase(temp);	       /* 0 <= noborrow <= 1 */
	 *wPtr++  = modBase(temp);
      }						     /* noborrow = 1 */
#else
      i = v->size;
      temp = u->size - i;
      if (temp > 0) {
	 memcpy(wPtr + i, uPtr + i, temp * sizeof(digit));
      }
      if (memsubw(wPtr, uPtr, v->value, i)) {	     /* trashes uPtr */
         memdecw(wPtr + i, temp);
      }
      wPtr += w->size;
#endif
      do {						/* normalize */
	 if (*--wPtr != 0) break;
      } while (wPtr > w->value);
      w->size = (wPtr - w->value) + 1;
   }

   pdestroy(u);
   pdestroy(v);
   return presult(w);
}
