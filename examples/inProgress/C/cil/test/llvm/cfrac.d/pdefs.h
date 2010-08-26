/*
 * +------------------------------------------------------------------+
 * |	     Private Math Library Definitions			      |
 * +------------------------------------------------------------------+
 */
/*
 * Optional assembly language 
 */
#ifdef ASM
#include "machineop.h"		/* 16-bit integer machine operations */
#define uModDiv(n, d, qp)	umoddiv16(n, d, qp)   /* slight help */
#else
#define uModDiv(n, d, qp)	(*(qp) = (n) / (d), (n) % (d))
#endif
#define uMul(u, v)		((u) * (v))	      /* fast enough */

/*
 * Optional alternate memory allocator
 */
#ifndef MYALLOC
#define allocate(size)	(char *) malloc(size)
#define deallocate(p)	free(p)
#else
extern char  *allocate();
extern void  deallocate();
#endif

/*
 * These next four types are used only used in this include file
 */
typedef	unsigned char	u8;				  /*  8 bits */
typedef unsigned short	u16;				  /* 16 bits */
typedef unsigned long	u32;			  	  /* 32 bits */
typedef u8           	boolean;		          /*  1 bit  */

#define BASE	  	65536		/* Base * (Base-1) <= MAXINT */

/*
 * Operations on Base (unsigned math)
 */
#define modBase(u)	((u) & 0xffff)		/* remainder on Base */
#define divBase(u)	((u) >> 16)		/* divide    by Base */
#define mulBase(u)	((u) << 16)		/* multiply  by Base */

/*
 * The type of a variable used to store intermediate results.  
 * This should be the most efficient unsigned int on your machine.
 */
typedef u32		accumulator;	     /* 0..(Base * Base) - 1 */

/*
 * The type of a single digit
 */
typedef u16      	digit;				/* 0..Base-1 */

/*
 * The type of a digit index (the largest number of digits - 1)
 * Determines the maximum representable precision (not usually changed)
 */
typedef u16      	posit;				 /* 0..size  */

typedef unsigned short	prefc;			/* in precision.h also */
/*
 * End of area which needs to be modified
 */

#define false     	0
#define true	  	1

typedef digit	      	digitString[1];	 	 /* dummy array type */
typedef digit     	*digitPtr;

/*
 * A normalized integer has the following attributes:
 *   -0 cannot occur
 *   all digits >= size assumed to be 0.  (no leading zero's)
 *   size > 0
 */
typedef struct {				
    prefc 	refcount;	/* reference count (must be 1st [for pref]) */
    posit	alloc;		/* allocated size      */
    posit       size;	 	/* number of digits    */
    boolean     sign;		/* sign: TRUE negative */
    digitString value;
} precisionType;

typedef precisionType	*precision;

/*
 * Overlay for cache of precisions
 */
typedef struct {
   precision 	next;		/* next item in list */
   short	count;		/* number of items in this sublist */
} cacheType;

typedef cacheType	*cachePtr;
/*
 * Maximum total memory consumed by cache = 
 *    LIMIT * (1 + SIZE * (PrecisionSize + sizeof(digit) * (SIZE-1) / 2))
 */
#ifndef CACHESIZE
#define CACHESIZE	32 		/* size of allocation cache */
#endif
#define CACHELIMIT	128 		/* Determines max mem used by cache */

#define PrecisionSize	(sizeof(precisionType) - sizeof(digitString))

/*
 * Function definitions are all in the global include file "mathdefs.h".
 */
extern precision 	palloc();	/* semi-private */
extern int 		pfree();	/* semi-private */
extern void 		pnorm();	/* semi-private */
