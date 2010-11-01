typedef struct Pfs {
   struct Pfs *next;
   precision  factor;
   unsigned   count;
} Pfactor;

typedef Pfactor    *FactorPtr;
typedef FactorPtr  FactorList;
typedef precision  (*pfunc)();	/* pointer to func returning precision */

#ifndef __STDC__

extern int       pprime();		/* test whether a number is prime */
extern precision pnextprime();		/* next prime >= it's argument */

extern precision pgcd();		/* greatest common divisor */
extern precision plcm();		/* least common multiple */
extern precision peuclid();		/* extended euclid's algorithm */

extern precision prho();		/* find factor using rho method */
extern precision pfermat();		/* find factor using Fermat's method */
extern precision pcfrac();		/* factor w/continued fractions */

extern int prhoInit();			/* alter parameters for rho method */
extern int pcfracInit();		/* alter paramteres for cfrac method */

extern precision  ptrial();		/* find factors using trial division */
extern precision  prfactor();		/* recursively factor a number */

extern void       paddfactor();		/* add a factor to a factorlist */
extern void       pputfactors();	/* print a factorlist */
extern void	  pfreefactors();	/* return a factorlist to memory */

#else

extern int       pprime(precision, unsigned trialCount);	
extern precision pnextprime(precision, unsigned trialCount);

extern precision pgcd(precision, precision);
extern precision plcm(precision, precision);
extern precision peuclid(precision, precision, precision *, precision *);

extern precision prho(precision n, unsigned *maxCount);
extern precision pfermat(precision n, unsigned *maxCount);
extern precision pcfrac(precision n, unsigned *maxCount);

extern int prhoInit(precision c, unsigned batchSize);
extern int pcfracInit(unsigned m, unsigned k, unsigned aborts);

extern precision  ptrial(precision n, unsigned *maxCount, FactorList *);
extern precision  prfactor(precision, unsigned *maxCount, pfunc, FactorList *);

extern void       paddfactor(FactorList *, precision);
extern void	  pfreefactors(FactorList *);

#ifndef BUFSIZE
#include <stdio.h>
#endif

extern void pputfactors(FILE *, FactorList);

#endif
