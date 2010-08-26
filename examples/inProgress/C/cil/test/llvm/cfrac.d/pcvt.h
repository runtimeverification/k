/*
 * Machine dependent file used for conversion routines
 *   (e.g. atop, ptoa, itop, ptoi, etc)
 */

/* 
 * For pXtop:  (X = {i,u,l,ul,d})
 */
#define	INTSIZE	  	2	/* floor(log[Base](2*(MAXINT+1))) */
#define	LONGSIZE	2	/* floor(log[Base](2*(MAXLONG+1))) */
#define	DOUBLESIZE  	129	/* double precision size = log[base](HUGE) */

/*
 * For ptoX
 */
#define MAXINT	  	(int)  ((unsigned int)  ~0 >> 1)
#define MAXLONG	  	(long) ((unsigned long) ~0 >> 1)
#define MAXUNSIGNED	(~ (unsigned int)  0)
#define MAXUNSIGNEDLONG	(~ (unsigned long) 0L)

#define MAXACC	  	(~ (accumulator)   0)

/*
 * aBase - Ascii base (ptoa)
 * There are aDigits Ascii digits per precision digit, pDigits.
 * At least one of { aDigits, pDigits } <= (MAXINT / the maximum posit value).
 */
#define	aDigits		525	/* aDigits/pDigits >~= log[aBase](Base) */
#define pDigits		109	/* 525/109=4.8165>log[10](65536)=4.816479931 */
#define	aBase		 10	/* string conversion base */
#define aDigit	 1000000000	/* must be power of aBase < MAXINT */
#define aDigitLog	  9	/* log[aBase] of aDigit */
