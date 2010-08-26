#include "pdefs.h"
#include "precision.h"

/*
 * Returns non-zero if u is odd
 */
int podd(u)
   precision u;
{
   register int res;

   (void) pparm(u);
   res = (*(u->value) & 1);
   pdestroy(u);
   return res;
}
