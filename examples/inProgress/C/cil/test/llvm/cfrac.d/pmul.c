#include "pdefs.h"
#include "precision.h"
#include <string.h>

#ifdef ASM_16BIT
#include "asm16bit.h"
#endif

/*
 *   Multiply u by v (assumes normalized)
 */
precision pmul(u, v)
   register precision v;			/* register a5 on 68000 */
#ifdef ASM_16BIT
   register precision u;			/* register a4 */
{
#else
   precision u;
{
   digitPtr vPtr;
   register digitPtr uPtr, wPtr, HiDigit;
   register accumulator	  temp;	       /* 0 <= temp < base * base */   /* d7 */
   register digit 	  vdigit;				       /* d6 */
#endif
   register digit	  hi; 			/* 0 <= hi < base */   /* d5 */
   precision w;

   (void) pparm(u);
   (void) pparm(v);
   /*
    * Check for multiply by zero.  Helps prevent wasted storage and -0
    */
   if (peqz(u) || peqz(v)) {
      w = palloc(1);
      if (w == pUndef) return w;

      w->sign	  = false;
      w->value[0] = 0;
   } else {
      if (u->size < v->size) { /* u is biggest number (for inner loop speed) */
	 w = u; u = v; v = w;
      }

      w = palloc(u->size + v->size);
      if (w == pUndef) return w;

      w->sign = (u->sign != v->sign);

#ifndef ASM_16BIT
      uPtr = u->value;
      vPtr = v->value;
      wPtr = w->value + u->size;			 /* this is correct! */
      do {
	 *--wPtr = 0;
      } while (wPtr > w->value);

      vPtr    = v->value;
      HiDigit = u->value + u->size;
      do {
	 uPtr	= u->value;
	 wPtr	= w->value + (vPtr - v->value);
	 hi	= 0;
	 vdigit = *vPtr;
	 do {	  
	    temp    = uMul(vdigit, *uPtr++);	/* 0 <= temp <= (base-1)^2   */
	    temp   += *wPtr;			/* 0 <= temp <= base(base-1) */
	    temp   += hi;			/* 0 <= temp < base * base   */
	    hi	    = divBase(temp);		/* 0 <= hi < base	     */
	    *wPtr++ = modBase(temp); 
	 } while (uPtr < HiDigit);
	 *wPtr++    = hi;
      } while (++vPtr < v->value + v->size);
#else
      hi = memmulw(w->value, u->value, u->size, v->value, v->size);
#endif
      if (hi == 0) {
	 --(w->size);				/* normalize */
      }
   }

   pdestroy(u);
   pdestroy(v);
   return presult(w);
}
