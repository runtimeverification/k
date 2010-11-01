#include "pdefs.h"
#include "precision.h"
#include <string.h>

#ifdef ASM_16BIT
#include "asm16bit.h"
#endif

/*
 * Add 
 *
 * This will work correctly if -0 is passed as input
 */
precision padd(u, v)
   register precision v;
#ifndef ASM_16BIT
   precision u;
{
   register digitPtr	wPtr, uPtr, vPtr;
#else
   register precision u;
{
   register digitPtr	wPtr;
   digitPtr		uPtr;
#endif
   precision		w;		       /*  function result   */
   register accumulator temp;		       /* 0 <= temp < 2*base */
   register digit	carry;		       /* 0 <= carry <= 1 */
#ifdef ASM_16BIT
   register int		size;
#endif

   (void) pparm(u);
   (void) pparm(v);
   if (u->sign != v->sign) {	 /* Are we are actually subtracting? */
      w = pUndef;
      if (v->sign) {
	 v->sign = !v->sign;			/* can't generate -0 */
	 pset(&w, psub(u, v));
	 v->sign = !v->sign;
      } else {
	 u->sign = !u->sign;			/* can't generate -0 */
	 pset(&w, psub(v, u));
	 u->sign = !u->sign;
      }
   } else {
      if (u->size < v->size) {	       /* u is always biggest number */
	 w = u; u = v; v = w;
      }

      w = palloc(u->size+1);		/* there is at most one added digit */
      if (w == pUndef) return w;		 /* arguments not destroyed */

      w->sign = u->sign;

      uPtr    = u->value;
      wPtr    = w->value;
#ifndef ASM_16BIT
      vPtr    = v->value;
      carry   = 0;
      do {				/* Add digits in both args */
	 temp	 = *uPtr++ + *vPtr++;	/* 0 <= temp < 2*base-1	   */
	 temp	+= carry;		/* 0 <= temp < 2*base	   */
	 carry	 = divBase(temp);	/* 0 <= carry <= 1	   */
	 *wPtr++ = modBase(temp);	/* mod has positive args   */
      } while (vPtr < v->value + v->size);

      while (uPtr < u->value + u->size) {	/* propogate carry */
	 temp	 = *uPtr++ + carry;		    
	 carry	 = divBase(temp);			   
	 *wPtr++ = modBase(temp);	       
      }
      *wPtr = carry;
#else
      size  = v->size;
      temp  = u->size - size;
      carry = memaddw(wPtr, uPtr, v->value, size);
      if (temp > 0) {
	 memcpy(wPtr + size, uPtr + size, temp * sizeof(digit));
	 if (carry) {
	    carry = memincw(wPtr + size, temp);
	 }
      }
      wPtr[u->size] = carry;		/* yes, I do mean u->size */
#endif
      if (carry == 0) {
	 --(w->size);
      }
   }

   pdestroy(u);
   pdestroy(v);
   return presult(w);
}
