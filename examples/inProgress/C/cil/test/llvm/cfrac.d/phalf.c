#include <string.h>
#include "pdefs.h"
#include "precision.h"

#ifdef ASM_16BIT
#include "asm16bit.h"
#endif

/*
 * Divide a precision by 2 
 */
precision phalf(u)
   register precision u;
{
#ifdef ASM_16BIT
   register precision w;
   register posit usize;

   pparm(u);
   usize = u->size;
   w = palloc(usize);
   if (w == pUndef) return w;

   w->sign = u->sign;
   (void) memcpy(w->value, u->value, usize * sizeof(digit));

   memlsrw(w->value, usize);		/* 68000 assembly language routine */
   if (usize > 1 && w->value[usize-1] == (digit) 0) {	      /* normalize */
      --(w->size);
   }
   pdestroy(u);
   return presult(w);
#else
   return pdiv(u, ptwo);
#endif
}
