#include "pdefs.h"
#include "precision.h"
#ifdef ASM_16BIT
#include "asm16bit.h"
#endif

/*
 * Single-digit remainder
 */
int pimod(u, v)
   register precision u;
   int 	    v;
{
#ifndef ASM_16BIT
   register digitPtr	uPtr;
   register accumulator temp;		       /* 0 <= temp < base^2 */
#endif
   register digit	r = 0, d;		/* 0 <= r,d < base */
   register int res = 0;

   (void) pparm(u);
   if (v < 0) d = (digit) -v; else d = (digit) v;
   if (d >= BASE) {
      errorp(PDOMAIN, "pimod", "divisor too big for single digit");
      goto done;
   } 
   if (d == 0) {
      errorp(PDOMAIN, "pimod", "divide by zero");
      goto done;
   } 
#ifndef ASM_16BIT
   uPtr = u->value + u->size;
   r    = 0;			  	/* r is current remainder */
   do {
       temp  = mulBase(r);		/* 0 <= temp <= (base-1)^2 */
       temp += *--uPtr;			/* 0 <= temp <= base(base-1) */
       r     = temp % d; 		/* 0 <= r < base */
   } while (uPtr > u->value);
#else
   r = memmodw1(u->value, u->size, d);
#endif

   res = (int) r;
   if (u->sign) res = -res;
done:
   pdestroy(u);
   return res;
}
