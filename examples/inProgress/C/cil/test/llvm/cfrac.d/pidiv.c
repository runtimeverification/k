#include "pdefs.h"
#include "precision.h"
#ifdef ASM_16BIT
#include "asm16bit.h"
#endif

/*
 * Single-digit divide
 */
precision pidiv(u, v)
   register precision u;
   int 	    v;
{
#ifndef ASM_16BIT
   register digitPtr	uPtr, qPtr;
   register accumulator temp;		       /* 0 <= temp < base^2 */
#endif
   register digit	r, d;			   /* 0 <= r,d < base */
   register posit	m;
   register precision	q;

   (void) pparm(u);

   if (v < 0) d = (digit) -v; else d = (digit) v;
   if (d >= BASE) {
      q = pnew(errorp(PDOMAIN, "pidiv", "divisor too big for single digit"));
      goto done;
   } 
   if (d == 0) {
      q = pnew(errorp(PDOMAIN, "pidiv", "divide by zero"));
      goto done;
   } 
   m = u->size;
   q = palloc(m);
   if (q == pUndef) goto done;

#ifndef ASM_16BIT
   qPtr = q->value + m;
   uPtr = u->value + m;
   r    = 0;			  		/* r is current remainder */
   do {
       temp  = mulBase(r);			/* 0 <= temp <= (base-1)^2   */
       temp += *--uPtr;			/* 0 <= temp <= base(base-1) */
       r     = uModDiv(temp, d, --qPtr); 	/* 0 <= r < base */
   } while (uPtr > u->value);
#else
   r = memdivw1(q->value, u->value, m, d);
#endif
   /*
    * normalize q
    */
   if (m > 1 && q->value[m-1] == 0) {
      --(q->size);
   }
   q->sign = (u->sign != (v < 0));
   if (q->size == 1 && *(q->value) == 0) q->sign = false;
done:
   pdestroy(u);
   return presult(q);
}
