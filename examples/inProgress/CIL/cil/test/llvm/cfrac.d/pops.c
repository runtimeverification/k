#ifdef DEBUGOPS
#include <stdio.h>
#endif
/*
 *	High Precision Math Library
 *
 *	Written by Dave Barrett					2/23/83
 *	Translated from modcal to pascal			4/30/84
 *	Mod portability fixed; removed floor function		5/14/84
 *	Fixed numerous bugs and improved robustness		5/21/84
 *	Translated to C						6/14/84
 *	Changed precision to be determined at run-time		5/19/85
 *	Added dynamic allocation				7/21/85
 *	Combined unsigned math and integer math			8/01/85
 *	Fixed Bug in pcmp					7/20/87 
 *	Fixed handling of dynamic storage (refcount added)	7/20/87
 *	Final debugging of current version             		8/22/87
 *	Fixed many bugs in various routines, wrote atop		2/07/89
 *	Tuned for speed, fixed overflow problems		3/01/89
 *	Removed refcounts, more tuning, removed pcreate		3/16/89
 *	Added cmp macros, change name of pzero, added pshift	4/29/89
 *	Repaired operation order bugs in pdiv, calc.c		5/15/91
 *      Added pdiv macro, split out pcmp, pabs, much cleanup	5/21/91
 *
 *	warning! The mod operation with negative arguments not portable.
 *		 I have therefore avoided it completely with much pain.
 *	
 *	The following identities have proven useful:
 *
 *	given:	a %  b = a - floor(a/b) * b
 *	then : -a % -b = -(a % b)
 *	       -a %  b = -( a % -b) = b - a % b (a % b != 0)
 *		a % -b = -(-a % b) = a % b - b	(a % b != 0)
 *
 *	given:	a %  b =  a - a / b * b
 *	then : -a % -b = -a % b = -(a % b)
 *		a % -b =  a % b
 *
 *	Also, be very careful of computations in the inner loops.  Much
 *	work has been done to make sure the compiler does not re-arrange
 *	expressions to cause an overflow. The compiler may still be doing
 *	unnecessary type conversions.
 *  
 * NOTES:
 *
 *	The ptoa routine creates storage which is likely to be forgotton.
 *
 *	A function returning a result must use the result.  If it doesn't
 *	the storage is never freed.  For example: itop(2); by itself
 *	You must make sure to pdestroy the result.
 *
 *	An error (out of storage) fails to deallocate u and v.
 *
 *	psub, pcmp, pdiv, and pmul all assume normalized arguments.
 *
 * This file contains the storage management-specific code:
 *     palloc, pfree, pset -- together these account for 45% of execution time
 */
#include <string.h>
#include "pdefs.h"	/* private include file */
#include "precision.h"	/* public include file for forward refs */

cacheType pcache[CACHESIZE];
static char ident[] = 
   " @(#) libprecision.a version 2.00  3-May-91 by Dave Barrett\n";

/*
 * normalize (used by div and sub)
 *   remove all leading zero's 
 *   force positive sign if result is zero
 */
void pnorm(u)
   register precision u;
{
   register digitPtr uPtr;

   uPtr = u->value + u->size;
   do {
      if (*--uPtr != 0) break;
   } while (uPtr > u->value);

   if (uPtr == u->value && *uPtr == 0) u->sign = false;

   u->size = (uPtr - u->value) + 1;		/* normalize */
}

/*
 * Create a number with the given size (private) (very heavily used)
 */
precision palloc(size)
   register posit size;
{
   register precision w;
   register cacheType *kludge = pcache + size;	/* for shitty compilers */

#ifndef NOMEMOPT
   if (size < CACHESIZE && (w = kludge->next) != pUndef) {
      kludge->next = ((cacheType *) w)->next;
      --kludge->count;
   } else {
#endif
      w = (precision) allocate(PrecisionSize + sizeof(digit) * size);
      if (w == pUndef)  {
	 w = errorp(PNOMEM, "palloc", "out of memory");
	 return w;
      }
#ifndef NOMEMOPT
   }
#endif
   w->refcount = 1;
   w->size     = w->alloc = size;
#ifdef DEBUGOPS
   printf("alloc %.8x\n", w); 
   fflush(stdout);
#endif
   return w;
}

/*
 * (Very heavily used: Called conditionally pdestroy)
 * (should be void, but some compilers can't handle it with the macro)
 */
int pfree(u)
   register precision u;
{
   register posit size;
   register cacheType *kludge; 	/* for shitty compilers */

#ifdef DEBUGOPS
   printf("free  %.8x\n", u); 
   fflush(stdout);
#endif

   size = u->alloc;

   kludge = pcache + size;
#ifndef NOMEMOPT
   if (size < CACHESIZE && kludge->count < CACHELIMIT) {
      ((cacheType *) u)->next = kludge->next;
      kludge->next = u;
      kludge->count++;
   } else {
#endif
      deallocate(u);
#ifndef NOMEMOPT
   }
#endif
   return 0;
}

/*
 * User inteface:
 *
 * Rules:
 *    a precision must be initialized to pUndef or to result of pnew.
 *    a precision pointer must point to a precision or be pNull
 *    pUndef may not be passed as an rvalue into a function
 *    pNull  may not be passed as an lvalue into a function
 *   
 *    presult and pdestroy are the only functions which may be passed pUndef
 */

/*
 * assignment with verification (slower, but helpful for bug detect)
 * It would be nice if this routine could detect pointers to incorrect
 * or non-living areas of memory.
 *
 * We can't check for undefined rvalue because we want to allow functions
 * to return pUndef, and then let the application check for it after assigning
 * it to a variable.
 *
 * usage: pset(&i, j);
 */
precision psetv(up, v)
   register precision *up, v;
{
   register precision u;

#ifdef DEBUGOPS
   printf("psetv %.8x %.8x ", up, v);
#endif
#ifdef DEBUGOPS
   printf("->%u", v->refcount);
#endif
   if (up == pNull) {
      errorp(PDOMAIN, "pset", "lvalue is pNull");
   }
   u = *up;
#ifdef DEBUGOPS
   printf(" %.8x", u);
#endif
   *up = v;
   if (v != pUndef) {
      v->refcount++;
   }
   if (u != pUndef) { 
      if (u->sign & ~1) {		/* a minimal check */
	 errorp(PDOMAIN, "pset", "invalid precision");
      }
      if (--(u->refcount) == 0) {
#ifdef DEBUGOPS
	 printf("->%u", u->refcount);
#endif
	 pfree(u);
      }
   }
#ifdef DEBUGOPS
   putchar('\n');
   fflush(stdout);
#endif
   return v;
}

precision pparmv(u)
   register precision u;
{
#ifdef DEBUGOPS
   printf("pparm %.8x\n", u);
   fflush(stdout);
#endif
   if (u == pUndef) {
      errorp(PDOMAIN, "pparm", "undefined function argument");
   }
   if (u->sign & ~1) {		/* a minimal check */
      errorp(PDOMAIN, "pparm", "invalid precision");
   }
   u->refcount++;
   return u;
}

/*
 * Function version of unsafe pparmq macro
 */
precision pparmf(u)
   register precision u;
{
   if (u != pUndef) {
      u->refcount++;
   }
   return u;
}

/*
 * Function version of pdestroy macro
 */
void pdestroyf(u)
   register precision u;
{
   if (u != pUndef && --u->refcount == 0) {
      pfree(u);
   }
}

#ifndef __GNUC__		/* inline in header file */
/*
 * We cannot allow this to be a macro because of the probability that it's
 * argument will be a function (e.g. utop(2))
 */
precision pnew(u) 
   register precision u;
{
   u->refcount++;
   return u;
}

/*
 * Cannot be a macro because of function argument possibility
 */
precision presult(u)
   register precision u;
{
   if (u != pUndef) {
      --(u->refcount);
   }
   return u;
}

/*
 * Quick but dangerous assignment
 *
 * Assumes: target not pNull and source not pUndef
 */
precision psetq(up, v) 
   register precision *up, v;
{
   register precision u = *up;		/* up may NOT be pNULL! */

   *up = v;				/* up may be &v, OK */
   if (v != pUndef) { 		/* to allow:  x=func(); if (x==pUndef) ... */
      v->refcount++;
   }
   if (u != pUndef && --(u->refcount) == 0) {
      pfree(u);
   }
   return v;
}
#endif

#if 0			/* original assignment code */
precision pset(up, v)
   register precision *up, v;
{
   register precision u;

   if (v != pUndef) v->refcount++;
   if (up == pNull) {		/* useful voiding parameters (pdiv) */
      pdestroy(v);
      return pUndef;
   }
   u = *up;
   if (u != pUndef) {		/* useful to force initial creation */
      pdestroy(u);
   }
   *up = v;		/* notice that v may be pUndef which is OK! */
   return v;			  /* no presult! This is a variable */
}
#endif
