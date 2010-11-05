/*
 * pcfrac: Implementation of the continued fraction factoring algoritm
 *
 * Every two digits additional appears to double the factoring time
 * 
 * Written by Dave Barrett (barrett%asgard@boulder.Colorado.EDU)
 */
#include <string.h>
#include <stdio.h>
#include <math.h>

#ifdef __STDC__
#include <stdlib.h>
#endif
#include "precision.h"
#include "pfactor.h"

extern int verbose;

unsigned cfracNabort  = 0;
unsigned cfracTsolns  = 0;
unsigned cfracPsolns  = 0;
unsigned cfracT2solns = 0;
unsigned cfracFsolns  = 0;

extern unsigned short primes[];
extern unsigned primesize;

typedef unsigned *uptr;
typedef uptr	 uvec;
typedef unsigned char *solnvec;
typedef unsigned char *BitVector;

typedef struct SolnStruc {
   struct SolnStruc *next;
   precision x;		/* lhs of solution */
   precision t;		/* last large prime remaining after factoring */
   precision r;		/* accumulated root of pm for powers >= 2 */
   BitVector e;		/* bit vector of factorbase powers mod 2 */
} Soln;

typedef Soln *SolnPtr;

#define BPI(x)	((sizeof x[0]) << 3)

void setBit(bv, bno, value)
   register BitVector bv;
   register unsigned bno, value;
{
   bv  += bno / BPI(bv);
   bno %= BPI(bv);
   *bv |= ((value != 0) << bno);
}

unsigned getBit(bv, bno)
   register BitVector bv;
   register unsigned bno;
{
   register unsigned res;

   bv  += bno / BPI(bv);
   bno %= BPI(bv);
   res  = (*bv >> bno) & 1;

   return res;
}

BitVector newBitVector(value, size)
   register solnvec value;
   unsigned size;
{
   register BitVector res;
   register solnvec  vp = value + size;
   unsigned msize = ((size + BPI(res)-1) / BPI(res)) * sizeof res[0];

   res = (BitVector) malloc(msize);
   if (res == (BitVector) 0) return res;

   memset(res, '\0', msize);
   do {
      if (*--vp) {
	 setBit(res, vp - value, (unsigned) *vp);
      }
   } while (vp != value);
   return res;
}

void printSoln(stream, prefix, suffix, pm, m, p, t, e)
   FILE *stream;
   char *prefix, *suffix;
   register unsigned *pm, m;
   precision p, t;
   register solnvec e;
{
   register unsigned i, j = 0;

   for (i = 1; i <= m; i++) j += (e[i] != 0);

   fputs(prefix, stream); 
   fputp(stream, pparm(p)); fputs(" = ", stream);
   if (*e & 1) putc('-', stream);  else putc('+', stream);
   fputp(stream, pparm(t)); 

   if (j >= 1) fputs(" *", stream);
   do {
      e++;
      switch (*e) {
      case 0: break;
      case 1: fprintf(stream, " %u", *pm); break;
      default:
	 fprintf(stream, " %u^%u", *pm, (unsigned) *e);
      }
      pm++;
   } while (--m);

   fputs(suffix, stream); 
   fflush(stream);
   pdestroy(p); pdestroy(t);
}

/*
 * Combine two solutions 
 */
void combineSoln(x, t, e, pm, m, n, bp)
   precision *x, *t, n;
   uvec	     pm;
   register  solnvec e;
   unsigned  m;
   SolnPtr   bp;
{
   register unsigned j;

   (void) pparm(n);
   if (bp != (SolnPtr) 0) {
      pset(x, pmod(pmul(bp->x, *x), n));
      pset(t, pmod(pmul(bp->t, *t), n));
      pset(t, pmod(pmul(bp->r, *t), n));
      e[0] += getBit(bp->e, 0);
   }
   e[0] &= 1;
   for (j = 1; j <= m; j++) {
      if (bp != (SolnPtr) 0) e[j] += getBit(bp->e, j);
      if (e[j] > 2) {
	 pset(t, pmod(pmul(*t, 
	    ppowmod(utop(pm[j-1]), utop((unsigned) e[j]>>1), n)), n));
	 e[j] &= 1;
      } else if (e[j] == 2) {
	 pset(t, pmod(pmul(*t, utop(pm[j-1])), n));
	 e[j] = 0;
      }
   }
   pdestroy(n);
}

/*
 * Create a normalized solution structure from the given inputs
 */
SolnPtr newSoln(n, pm, m, next, x, t, e)
   precision n;
   unsigned  m;
   uvec     pm;
   SolnPtr next;
   precision x, t;
   solnvec e;
{
   SolnPtr bp = (SolnPtr) malloc(sizeof (Soln));

   if (bp != (SolnPtr) 0) {
      bp->next = next;
      bp->x = pnew(x);
      bp->t = pnew(t);
      bp->r = pnew(pone);
      /*
       * normalize e, put the result in bp->r and e
       */
      combineSoln(&bp->x, &bp->r, e, pm, m, pparm(n), (SolnPtr) 0);
      bp->e = newBitVector(e, m+1);			/* BitVector */
   }

   pdestroy(n);
   return bp;
}

void freeSoln(p)
   register SolnPtr p;
{
   if (p != (SolnPtr) 0) {
      pdestroy(p->x);
      pdestroy(p->t);
      pdestroy(p->r);
      free(p->e);			/* BitVector */
      free(p);
   }
}

void freeSolns(p)
   register SolnPtr p;
{
   register SolnPtr l;
   
   while (p != (SolnPtr) 0) {
      l = p;
      p = p->next;
      freeSoln(l);
   }
}

SolnPtr findSoln(sp, t)
   register SolnPtr sp;
   precision t;
{
   (void) pparm(t);
   while (sp != (SolnPtr) 0) {
      if peq(sp->t, t) break;
      sp = sp->next;
   }
   pdestroy(t);
   return sp;
}

static unsigned pcfrac_k      = 1;
static unsigned pcfrac_m      = 0;
static unsigned pcfrac_aborts = 3;

/*
 * Structure for early-abort.  Last entry must be <(unsigned *) 0, uUndef>
 */
typedef struct {
   unsigned  *pm;	/* bound check occurs before using this pm entry */
   precision bound;	/* max allowable residual to prevent abort */
} EasEntry;

typedef EasEntry *EasPtr;

void freeEas(eas)
   EasPtr eas;
{
   register EasPtr ep = eas;

   if (ep != (EasPtr) 0) {
      while (ep->pm != 0) {
	 pdestroy(ep->bound);
	 ep++;
      }
      free(eas);
   }
}

/*
 * Return Pomerance's L^alpha (L = exp(sqrt(log(n)*log(log(n)))))
 */
double pomeranceLpow(n, y) 
   double n;
   double y;
{
   double lnN = log(n);
   double res = exp(y * sqrt(lnN * log(lnN)));
   return res;
}

/*
 * Pomerance's value 'a' from page 122 "of Computational methods in Number
 * Theory", part 1, 1982.
 */
double cfracA(n, aborts)
   double n;
   unsigned aborts;
{
   return 1.0 / sqrt(6.0 + 2.0 / ((double) aborts + 1.0));
}

/*
 * Returns 1 if a is a quadratic residue of odd prime p, 
 * p-1 if non-quadratic residue, 0 otherwise (gcd(a,p)<>1)
 */
#define plegendre(a,p) ppowmod(a, phalf(psub(p, pone)), p)

/*
 * Create a table of small primes of quadratic residues of n
 *
 * Input:   
 *    n      - the number to be factored
 *    k      - the multiple of n to be factored
 *    *m     - the number of primes to generate (0 to select best)
 *    aborts - the number of early aborts
 *
 * Assumes that plegendre # 0, for if it is, that pm is a factor of n.
 * This algorithm already assumes you've used trial division to eliminate
 * all of these!
 *
 * Returns: the list of primes actually generated (or (unsigned *) 0 if nomem)
 *          *m changed to reflect the number of elements in the list
 */
uvec pfactorbase(n, k, m, aborts)
   precision n;
   unsigned k;
   unsigned *m, aborts;
{
   double   dn, a;
   register unsigned short *primePtr = primes;
   register unsigned count = *m;
   unsigned maxpm = primes[primesize-1];
   unsigned *res  = (uvec) 0, *pm;
   precision nk   = pnew(pmul(pparm(n), utop(k)));

   if (*m == 0) {			/* compute a suitable m */
      dn    = ptod(nk);
      a     = cfracA(dn, aborts);
      maxpm = (unsigned) (pomeranceLpow(dn, a) + 0.5);
      do {
	 if ((unsigned) *primePtr++ >= maxpm) break;
      } while ((unsigned) *primePtr != 1);
      count = primePtr - primes;
      primePtr = primes;
   }
   /*
    * This m tends to be too small for small n, and becomes closer to 
    * optimal as n goes to infinity.  For 30 digits, best m is ~1.5 this m.
    * For 38 digits, best m appears to be ~1.15 this m. It's appears to be
    * better to guess too big than too small.
    */
   res = (uvec) malloc(count * sizeof (unsigned));
   if (res == (uvec) 0) goto doneMk;

   pm    = res;
   *pm++ = (unsigned) *primePtr++;		/* two is first element */
   count = 1;
   if (count != *m) do {
      if (picmp(plegendre(nk, utop((unsigned) *primePtr)), 1) <= 0) { /* 0,1 */
	 *pm++ = *primePtr;
	 count++;
	 if (count == *m) break;
	 if ((unsigned) *primePtr >= maxpm) break;
      }
      ++primePtr;
   } while (*primePtr != 1);
   *m = count;

doneMk:
   pdestroy(nk);
   pdestroy(n);
   return res;
}

/*
 * Compute Pomerance's early-abort-stragegy
 */
EasPtr getEas(n, k, pm, m, aborts)
   precision n;
   unsigned k, *pm, m, aborts;
{
   double x    = 1.0 / ((double) aborts + 1.0);
   double a    = 1.0 / sqrt(6.0 + 2.0 * x);
   double ax   = a * x, csum = 1.0, tia = 0.0;
   double dn, dpval, dbound, ci;
   unsigned i, j, pval;

   precision bound = pUndef;
   EasPtr   eas;
   
   if (aborts == 0) return (EasPtr) 0;

   eas = (EasPtr) malloc((aborts+1) * sizeof (EasEntry));
   if (eas == (EasPtr) 0) return eas;

   dn   = ptod(pmul(utop(k), pparm(n)));	/* should this be n ? */
   for (i = 1; i <= aborts; i++) {
      eas[i-1].pm = (unsigned *) 0;
      eas[i-1].bound = pUndef;
      tia        += ax;
      ci          = 4.0 * tia * tia / (double) i;
      csum       -= ci;
      dpval 	  = pomeranceLpow(dn, tia);
      dbound      = pow(dn, 0.5 * csum);

      pval	  = (unsigned) (dpval + 0.5);
      pset(&bound, dtop(dbound));
      for (j = 0; j < m; j++) {
	 if (pm[j] >= pval) goto foundpm;
      }
      break;
foundpm:
      if (verbose > 1) {
	 printf(" Abort %u on p = %u (>=%u) and q > ", i, pm[j], pval);
	 fputp(stdout, bound);  putc('\n', stdout);
	 fflush(stdout);
      }
      eas[i-1].pm = &pm[j];
      pset(&eas[i-1].bound, bound);
   }
   eas[i-1].pm = (unsigned *) 0;
   eas[i-1].bound = pUndef;

   pdestroy(bound);
   pdestroy(n);

   return eas;
}

/*
 * Factor the argument Qn using the primes in pm.  Result stored in exponent
 * vector e, and residual factor, f.  If non-null, eas points to a list of
 * early-abort boundaries.
 *
 * e is set to the number of times each prime in pm divides v.
 *
 * Returns: 
 *    -2 - if factoring aborted because of early abort
 *    -1 - factoring failed
 *     0 - if result is a "partial" factoring
 *     1 - normal return (a "full" factoring)
 */
int pfactorQ(f, t, pm, e, m, eas)
   precision *f;
   precision t;
   register unsigned *pm;
   register solnvec  e;
   register unsigned m;
   EasEntry *eas;
{
   precision maxp  = pUndef; 
   unsigned  maxpm = pm[m-1], res = 0;
   register unsigned *pp = (unsigned *) 0;
   
   (void) pparm(t);

   if (eas != (EasEntry *) 0) {
      pp = eas->pm;
      pset(&maxp, eas->bound);
   }

   memset((char *) e, '\0', m * sizeof e[0]);  /* looks slow here, but isn't */

   while (peven(t)) {		/* assume 2 1st in pm; save time */
      pset(&t, phalf(t));
      (*e)++;
   }
   --m;

   do {
      e++; pm++;
      if (pm == pp) {		/* check for early abort */
	 if (pgt(t, maxp)) {
	    res = -2;
	    goto gotSoln;
	 }
	 eas++;
	 pp = eas->pm;
	 pset(&maxp, eas->bound);
      }
      while (pimod(t, (int) *pm) == 0) {
	 pset(&t, pidiv(t, (int) *pm));
	 (*e)++;
      }
   } while (--m != 0);
   res = -1;
   if (picmp(t, 1) == 0) {
      res = 1;
   } else if (picmp(pidiv(t, (int) *pm), maxpm) <= 0) {
#if 0 		/* it'll never happen;  Honest! If so, pm is incorrect. */
      if (picmp(t, maxpm) <= 0) {
	 fprintf(stderr, "BUG: partial with t < maxpm! t = "); 
	 fputp(stderr, t); putc('\n', stderr);
      }
#endif
      res = 0;
   }
gotSoln:
   pset(f, t);
   pdestroy(t); pdestroy(maxp);
   return res;
}

/*
 * Attempt to factor n using continued fractions (n must NOT be prime)
 *
 * n        - The number to attempt to factor
 * maxCount - if non-null, points to the maximum number of iterations to try.
 *
 * This algorithm may fail if it get's into a cycle or maxCount expires
 * If failed, n is returned.
 *
 * This algorithm will loop indefinitiely in n is prime.
 *
 * This an implementation of Morrison and Brillhart's algorithm, with 
 * Pomerance's early abort strategy, and Knuth's method to find best k.
 */
precision pcfrac(n, maxCount)
   precision n;
   unsigned *maxCount;
{
   unsigned k      = pcfrac_k;
   unsigned m      = pcfrac_m;
   unsigned aborts = pcfrac_aborts;
   SolnPtr  oddt   = (SolnPtr) 0, sp, bp, *b;
   EasPtr   eas    = (EasPtr) 0;
   uvec     pm     = (uvec) 0; 
   solnvec  e	   = (solnvec) 0;
   unsigned bsize, s = 0, count = 0;
   register unsigned h, j;
   int i;

   precision t = pUndef,
      r  = pUndef, twog   = pUndef,  u = pUndef, lastU  = pUndef,
      Qn = pUndef, lastQn = pUndef, An = pUndef, lastAn = pUndef,
      x  = pUndef, y      = pUndef, qn = pUndef,     rn = pUndef;

   precision res = pnew(pparm(n));		/* default res is argument */
   
   pm = pfactorbase(n, k, &m, aborts); 		/* m may have been reduced */

   bsize  = (m+2) * sizeof (SolnPtr);
   b      = (SolnPtr *) malloc(bsize);
   if (b == (SolnPtr *) 0) goto nomem;

   e = (solnvec) malloc((m+1) * sizeof e[0]); 
   if (e == (solnvec) 0) {
nomem:
      errorp(PNOMEM, "pcfrac", "out of memory");
      goto bail;
   }

   memset(b, '\0', bsize);				 /* F1: Initialize */
   if (maxCount != (unsigned *) 0) count = *maxCount;
   cfracTsolns = cfracPsolns = cfracT2solns = cfracFsolns = cfracNabort = 0;

   eas = getEas(n, k, pm, m, aborts);		/* early abort strategy */

   if (verbose > 1) {
      fprintf(stdout, "factorBase[%u]: ", m);
      for (j = 0; j < m; j++) {
	 fprintf(stdout, "%u ", pm[j]);
      }
      putc('\n', stdout);
      fflush(stdout);
   }

   pset(&t,      pmul(utop(k), n)); 		/* E1: Initialize */
   pset(&r,      psqrt(t));			/* constant: sqrt(k*n) */
   pset(&twog,   padd(r, r));			/* constant: 2*sqrt(k*n) */
   pset(&u,      twog);				/* g + Pn */
   pset(&lastU,  twog);
   pset(&Qn,     pone);
   pset(&lastQn, psub(t, pmul(r, r)));
   pset(&An,     pone);
   pset(&lastAn, r);
   pset(&qn,     pzero);

   do {
F2:
      do {
	 if (--count == 0) goto bail;
	 pset(&t, An);
	 pdivmod(padd(pmul(qn, An), lastAn), n, pNull, &An);  	/* (5) */
	 pset(&lastAn, t);

	 pset(&t, Qn);
	 pset(&Qn, padd(pmul(qn, psub(lastU, u)), lastQn));	/* (7) */
	 pset(&lastQn, t);

	 pset(&lastU, u);

	 pset(&qn, pone);		/* eliminate 40% of next divmod */
	 pset(&rn, psub(u, Qn));
	 if (pge(rn, Qn)) {
	    pdivmod(u, Qn, &qn, &rn);				/* (4) */
	 }
	 pset(&u, psub(twog, rn));				/* (6) */
	 s = 1-s;

	 e[0] = s;
	 i = pfactorQ(&t, Qn, pm, &e[1], m, eas);  	/* E3: Factor Qn */
	 if (i < -1) cfracNabort++;
	 /* 
	  * We should (but don't, yet) check to see if we can get a 
	  * factor by a special property of Qn = 1
	  */
	 if (picmp(Qn, 1) == 0) {
	    errorp(PDOMAIN, "pcfrac", "cycle encountered; pick bigger k");
	    goto bail;			/* we ran into a cycle; give up */
	 }
      } while (i < 0); 			/* while not a solution */

      pset(&x, An); 	/* End of Algorithm E; we now have solution: <x,t,e> */

      if (i == 0) {	/* if partial */
	 if ((sp = findSoln(oddt, t)) == (SolnPtr) 0) {
	    cfracTsolns++;
	    if (verbose >= 2) putc('.', stderr);
	    if (verbose > 3) printSoln(stdout, "Partial: ","\n", pm,m,x,t,e);
	    oddt = newSoln(n, pm, m, oddt, x, t, e);
	    goto F2;			/* wait for same t to occur again */
	 }
	 if (verbose > 3) printSoln(stdout, "Partial: ", " -->\n", pm,m,x,t,e);
	 pset(&t, pone);		/* take square root */
         combineSoln(&x, &t, e, pm, m, n, sp);
	 cfracT2solns++;
	 if (verbose) putc('#', stderr);
	 if (verbose > 2) printSoln(stdout, "PartSum: ", "", pm, m, x, t, e);
      } else {
	 combineSoln(&x, &t, e, pm, m, n, (SolnPtr) 0);		/* normalize */
	 cfracPsolns++;
	 if (verbose) putc('*', stderr);
	 if (verbose > 2) printSoln(stdout, "Full:    ", "", pm, m, x, t, e);
      }

      /* 
       * Crude gaussian elimination.  We should be more effecient about the
       * binary vectors here, but this works as it is.
       *
       * At this point, t must be pone, or t occurred twice
       *
       * Loop Invariants:  e[0:h] even
       *                   t^2 is a product of squares of primes
       *                   b[h]->e[0:h-1] even and b[h]->e[h] odd
       */
      h = m+1;
      do {
	 --h;
	 if (e[h]) {				/* F3: Search for odd */
	    bp=b[h];
	    if (bp == (SolnPtr) 0) { 		/* F4: Linear dependence? */
	       if (verbose > 3)  {
		  printSoln(stdout, " -->\nFullSum: ", "", pm, m, x, t, e); 
	       }
	       if (verbose > 2) putc('\n', stdout);
	       b[h] = newSoln(n, pm, m, bp, x, t, e);
	       goto F2;
	    }
	    combineSoln(&x, &t, e, pm, m, n, bp);
	 }
      } while (h != 0);
      /*
       * F5: Try to Factor: We have a perfect square (has about 50% chance)
       */
      cfracFsolns++;
      pset(&y, t);				/* t is already sqrt'd */

      switch (verbose) {
      case 0: break;
      case 1: putc('/', stderr); break;
      case 2: putc('\n', stderr); break;
      default: ;
	 putc('\n', stderr);
	 printSoln(stdout, " -->\nSquare:  ", "\n", pm, m, x, t, e); 
	 fputs("x,y:     ", stdout); 
	 fputp(stdout, x); fputs("  ", stdout);
	 fputp(stdout, y); putc('\n', stdout);
	 fflush(stdout);
      }
   } while (peq(x, y) || peq(padd(x, y), n));	/* while x = +/- y */

   pset(&res, pgcd(padd(x, y), n));		/* factor found at last */

   /*
    * Check for degenerate solution.  This shouldn't happen. Detects bugs.
    */
   if (peq(res, pone) || peq(res, n)) {
      fputs("Error!  Degenerate solution:\n", stdout);
      fputs("x,y:   ", stdout); 
      fputp(stdout, x); fputs(" ", stdout);
      fputp(stdout, y); putc('\n', stdout);
      fflush(stdout);
      abort();
   }

bail:
   /*malloc_stats();*/
   if (maxCount != (unsigned *) 0) *maxCount = count;

   if (b != (SolnPtr *) 0) for (j = 0; j <= m; j++) freeSoln(b[j]);
   freeEas(eas);
   freeSolns(oddt);
   free(e);
   free(pm);

   pdestroy(r);  pdestroy(twog);   pdestroy(u);  pdestroy(lastU);
   pdestroy(Qn); pdestroy(lastQn); pdestroy(An); pdestroy(lastAn);
   pdestroy(x);  pdestroy(y);      pdestroy(qn); pdestroy(rn);
   pdestroy(t);  pdestroy(n);

   return presult(res);
}

/*
 * Initialization for pcfrac factoring method
 *
 * k      - An integer multiplier to use for n (k must be < n)
 *            you can use findk to get a good value.  k should be squarefree
 * m      - The number of primes to use in the factor base
 * aborts - the number of early aborts to use
 */
int pcfracInit(m, k, aborts)
   unsigned m;
   unsigned k;
   unsigned aborts;
{
   pcfrac_m      = m;
   pcfrac_k      = k;
   pcfrac_aborts = aborts;
   return 1;
}
