#include <stdio.h>
#include "precision.h"

/*
 * Fatal error (user substitutable)
 *
 *   PNOMEM 	- out of memory (pcreate)
 *   PREFCOUNT 	- refcount negative (pdestroy)
 *   PUNDEFINED	- undefined value referenced (all)
 *   PDOMAIN	- domain error
 *	 pdivmod: divide by zero
 *	 psqrt:   negative argument
 *   POVERFLOW	- overflow
 *       itop:    too big
 */
precision errorp(errnum, routine, message)
   int errnum;
   char *routine;
   char *message;
{
   fputs(routine, stderr);
   fputs(": ", stderr);
   fputs(message, stderr);
   fputs("\n", stderr);
   abort();			/* remove this line if you want */
   return pUndef;
}
