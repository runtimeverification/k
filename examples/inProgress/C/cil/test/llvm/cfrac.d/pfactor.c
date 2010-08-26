#include <stdio.h>
#include "precision.h"
#include "pfactor.h"

void showfactors();


int main(argc, argv)
   int argc;
   char *argv[];
{
   precision n = pUndef;

   --argc;
   if (argc != 0) {
      do {
	 pset(&n, atop(*++argv));
	 showfactors(n);
      } while (--argc > 0);
   } else {
      do {
	 pset(&n, fgetp(stdin));
	 if (n == pUndef) break;
	 showfactors(n);
      } while (1);
   }
   pdestroy(n);
   return 0;
}

void showfactors(n)
   precision n;
{
   precision r = pUndef;
   FactorList factors = (FactorList) 0;

   (void) pparm(n);
   pset(&r, ptrial(n, (unsigned *) 0, &factors));
   fputp(stdout, n);
   fputs(" = ", stdout);
   pputfactors(stdout, factors);
   if pne(r, pone) {
      if pne(r, n) putc('*', stdout);
      if (!pprime(r, 16)) {
	 fputc('(', stdout); fputp(stdout, r); fputc(')', stdout);
      } else {
	 fputp(stdout, r);
      }
   }
   putc('\n', stdout);

   pfreefactors(&factors);
   pdestroy(r);
   pdestroy(n);
}
