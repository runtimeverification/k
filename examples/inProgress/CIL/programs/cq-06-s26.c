#include "cq-header.h"

int sec(pd0)                  /*  2.6  Hardware Characteristics     */
struct defs *pd0;
{
	setupTable(pd0) ;
   static char s[] = "VOLATILE: %3d bits in %ss.\n";
   // cme %e to %f
   static char s2[] = "VOLATILE: %f is the least number that can be added to 1. (%s).\n";

          /* Now, if anyone's interested, we publish the results.       */

   if(pd0->flgm != 0) {
     printf(s,pd0->cbits,"char");
     printf(s,pd0->ibits,"int");
     printf(s,pd0->sbits,"short");
     printf(s,pd0->lbits,"long");
     printf(s,pd0->ubits,"unsigned");
     printf(s,pd0->fbits,"float");
     printf(s,pd0->dbits,"double");
     printf(s2,pd0->fprec,"float");
     printf(s2,pd0->dprec,"double");
   }
          /* Since we are only exploring and perhaps reporting, but not 
             testing any features, we cannot return an error code.  */

   return 0;
}
#include "cq-main.h"
