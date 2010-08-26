#include "pdefs.h"
#include "precision.h"

static char cmpError[] = "Second arg not single digit";

/*
 * Single-digit compare
 */
int picmp(u, v)
   register precision u; 
   register int v;
{
   register int i;

   (void) pparm(u);

   if (u->sign) {
      i = -1;
      if (v < 0) {
	 if (-v >= BASE) {
	    errorp(PDOMAIN, "picmp", cmpError);
	 }
	 if (u->size == 1) {
	    i = - (int) *(u->value) - v;
	 }
      }
   } else {
      i = 1;
      if (v >= 0) {
	 if (v >= BASE) {
	    errorp(PDOMAIN, "picmp", cmpError);
	 }
	 if (u->size == 1) {
	    i = (int) *(u->value) - v;
	 }
      }
   }

   pdestroy(u);
   return i;
}
