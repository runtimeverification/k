/*
 * Arbitrary precision integer math package
 * 
 * (c) Copyright 1991 by David A. Barrett (barrett@asgard.UUCP)
 *
 * Not to be used for profit or distributed in systems sold for profit
 */
#ifndef BASE
typedef unsigned short	prefc;		/* reference counter type */
typedef prefc		*precision;	/* this a a private data structure */
extern	int		pfree();	/* free (private) */
#endif

typedef precision 	*pvector;	/* a vector of precision */
typedef pvector		*parray;	/* 2d array */

/*
 * Error values passed to errorp
 */
#define PNOERROR	0
#define PNOMEM		1
#define PREFCOUNT	2
#define PUNDEFINED	3
#define PDOMAIN		4
#define POVERFLOW	5

#define pUndef		((precision) 0)		/* An undefined value */
#define pNull		((precision *) 0)

#define peq(u, v)	(pcmp((u), (v)) == 0)
#define pne(u, v)	(pcmp((u), (v)) != 0)
#define pgt(u, v)	(pcmp((u), (v)) >  0)
#define plt(u, v)	(pcmp((u), (v)) <  0)
#define pge(u, v)	(pcmp((u), (v)) >= 0)
#define ple(u, v)	(pcmp((u), (v)) <= 0)

#define peqz(u)		(pcmpz(u) == 0)
#define pnez(u)		(pcmpz(u) != 0)
#define pltz(u)		(pcmpz(u) <  0)
#define pgtz(u)		(pcmpz(u) >  0)
#define plez(u)		(pcmpz(u) <= 0)
#define pgez(u)		(pcmpz(u) >= 0)

#define peven(u)	(!podd(u))
#define pdiv(u,v)	(pdivmod(u,v, (precision *) -1, pNull))
#define pmod(u,v)	(pdivmod(u,v, pNull, (precision *) -1))
#define pdivr(u,v,r)	(pdivmod(u,v, (precision *) -1, r))
#define pmodq(u,v,q)	(pdivmod(u,v, q, (precision *) -1))

/*
 * Application programs should only use the following definitions;
 *
 *    pnew, pdestroy, pparm, presult and pset
 *
 * Other variants are internal only!  
 * All are side-effect safe except for pparm and presult.
 * -DDEBUG will enable argument checking for pset and pparm
 */
#ifdef __GNUC__		/* inline is NOT ansii!  Sigh. */
static inline precision pnew(precision u) { (* (prefc *) u)++; return u; }
static inline void      pdestroy(precision u) {
   if (u != pUndef && --(*(prefc *) u) == 0) pfree(u);
}
static inline precision pparmq(precision u) { 
   if (u != pUndef) (* (prefc *) u)++; return u;
}
static inline precision presult(precision u) {
   if (u != pUndef) --(*(prefc *) u); return u;
}
static inline precision psetq(precision *up, precision v) {
   precision u = *up;
   *up = v;
   if (v != pUndef) (* (prefc *) v)++;
   if (u != pUndef && --(* (prefc *) u) == 0) pfree(u);
   return v;
}
#define pvoid(u)	pdestroy(u)
#else
#define pdestroy(u)     (void) ((u)!=pUndef&&--(*(prefc *)(u))==0&&pfree(u))
#define pparmq(u)	((u) != pUndef && (* (prefc *) (u))++, (u))
#define pvoid(u)	pdestroyf(u)
#endif


#ifdef PDEBUG
#define pset(u, v)	psetv(u, v)
#define pparm(u)	pparmv(u)
#else
#define pset(u, v)	psetq(u, v)
#define pparm(u)	pparmq(u)
#endif

#ifdef __STDC__		/* if ANSI compiler */
#ifndef __GNUC__
extern	precision 	pnew(precision);		/* initialization */
extern	precision 	presult(precision);		/* function result */
extern	precision	psetq(precision *, precision);	/* quick assignment */
#endif
extern	precision	psetv(precision *, precision); /* checked assignment */
extern	precision	pparmv(precision);	/* checked parameter */
extern	precision	pparmf(precision);	/* unchecked parameter (fn) */

extern	int		pcmpz(precision);		/* compare to zero */
extern	int		pcmp(precision, precision);	/* compare */
extern	int		picmp(precision, int);	        /* single digit cmp */

extern	precision	padd(precision, precision);	/* add */
extern	precision	psub(precision, precision);	/* subtract */
extern	precision	pmul(precision, precision);	/* multiply */

extern	precision	pdivmod(precision, precision, 
			        precision *q, precision *r);

extern 	precision	pidiv(precision, int);		/* single digit pdiv */
extern 	int		pimod(precision, int);		/* single digit pmod */
extern 	void		pidivmod(precision, int, 	/* single pdivmod */
				precision *q, int *r);

extern	precision	pneg(precision);		/* negate */
extern	precision	pabs(precision);		/* absolute value */
extern	int		podd(precision);		/* true if odd */
extern	precision	phalf(precision);		/* divide by two */

extern	precision	pmin(precision, precision);	/* minimum value */
extern	precision	pmax(precision, precision);	/* maximum value */

extern	precision	prand(precision);	/* random number generator */

extern	precision	itop(int);		/* int to precision */
extern	precision	utop(unsigned);		/* unsigned to precision */
extern	precision	ltop(long);		/* long to precision */
extern	precision	ultop(unsigned long);	/* unsigned long to precision */

extern	int		ptoi(precision);	/* precision to int */
extern	unsigned int	ptou(precision);	/* precision to unsigned */
extern	long		ptol(precision);	/* precision to long */
extern	unsigned long	ptoul(precision);	/* precision to unsigned long */

extern	precision	atop(char *);		/* ascii to precision */
extern	char		*ptoa(precision);	/* precision to ascii */

extern	int 		btop(precision *result, /* base to precision */
   char *src, unsigned size, int *digitmap, unsigned radix);

extern	int				/* precision to base */
   ptob(precision, char *result, unsigned size, char *alphabet, unsigned radix);

/*
 * Can't do prototyping for these unless stdio.h has been included 
 */
#ifdef BUFSIZ
extern	precision	fgetp(FILE *stream);	        /* input precision */
extern	int		fputp(FILE *stream, precision); /* output precision */
extern	int		
   fprintp(FILE *stream, precision, int minWidth); /* output within a field */
#else
extern	precision	fgetp();	        /* input precision */
extern	int		fputp(); 		/* output precision */
extern	int		fprintp(); 		/* output within a field */
#endif

extern	int		putp(precision);  	  /* stdout  with '\n' */

extern	void		pshow(precision);	  /* display debug info */
extern	precision	prandnum();		  /* debug and profil only */
extern	precision	pshift(precision, int);	  /* shift left */

extern	precision	errorp(int errnum, char *routine, char *message);

extern	precision	pzero, pone, ptwo;	  /* constants 0, 1, and 2 */
extern	precision	p_one;			  /* constant -1 */

extern	precision	psqrt(precision);	     /* square root */
extern	precision	pfactorial(precision);	     /* factorial */
extern	precision	pipow(precision, unsigned);  /* unsigned int power */
extern	precision	ppow(precision, precision);  /* precision power */
extern	precision
   ppowmod(precision, precision, precision);	     /* precision power mod m */
extern	int		plogb(precision, precision); /* log base b of n */

extern	precision	dtop(double);		/* double to precision */
extern	double		ptod(precision);	/* precision to double */

/*
 * vector operations
 */
pvector pvundef(pvector, unsigned size);	/* local variable entry */
void    pvdestroy(pvector, unsigned size);	/* local variable exit */

//pvector pvalloc(unsigned size);			/* pvec allocate */
void    pvfree(pvector, unsigned size);		/* pvec free */

pvector pvset(pvector, unsigned size, precision value);

#else

/*
 * Function versions of above if you still want side effects
 */

#ifndef __GNUC__
extern	precision 	pnew();		/* initialization */
extern	precision 	presult();	/* function result */
extern	precision	psetq();	/* quick assignment */
#endif
extern	precision	psetv(); 	/* checked assignment */
extern	precision	pparmv();	/* checked parameter */
extern	precision	pparmf();	/* unchecked parameter (fn) */

extern	int		pcmpz();	/* compare to zero */
extern	int		pcmp();		/* compare */
extern	int		picmp();	/* single digit compare */

extern	precision	padd();		/* add */
extern	precision	psub();		/* subtract */
extern	precision	pmul();		/* multiply */

extern	precision	pdivmod();	/* divide/remainder */
extern 	void		pidivmod();	/* single digit divide/remainder */
extern 	precision	pidiv();	/* single digit divide */
extern 	int		pimod();	/* single digit remainder */
extern	precision	pneg();		/* negate */
extern	precision	pabs();		/* absolute value */
extern	int		podd();		/* true if odd */
extern	precision	phalf();	/* divide by two */

extern	precision	pmin();		/* minimum value */
extern	precision	pmax();		/* maximum value */

extern	precision	prand();	/* random number generator */

extern	precision	itop();		/* int to precision */
extern	precision	utop();		/* unsigned to precision */
extern	precision	ltop();		/* long to precision */
extern	precision	ultop();	/* unsigned long to precision */

extern	int		ptoi();		/* precision to int */
extern	unsigned int	ptou();		/* precision to unsigned */
extern	long		ptol();		/* precision to long */
extern	unsigned long	ptoul();	/* precision to unsigned long */

extern	precision	atop();		/* ascii to precision */
extern	char		*ptoa();	/* precision to ascii */

extern	int		btop();		/* base to precision */
extern	int		ptob();		/* precision to base */

extern	precision	fgetp();	/* input a precision */
extern	int		fputp();	/* output a precision */
extern	int		putp();		/* output precision '\n' to stdout */
extern	int		fprintp();	/* output a precision within a field */

extern	void		pshow();	/* display debug info */
extern	precision	prandnum();	/* for debug and profil only */
extern	precision	pshift();	/* shift left */

extern	precision	errorp();	/* user-substitutable error handler */

extern	precision	pzero, pone, ptwo;	/* constants 0, 1, and 2 */
extern	precision	p_one;			/* constant -1 */

extern	precision	psqrt();	/* square root */
extern	precision	pfactorial();	/* factorial */
extern	precision	pipow();	/* unsigned int power */
extern	precision	ppow();		/* precision power */
extern	precision	ppowmod();	/* precision power mod m */
extern	int		plogb();	/* log base b of n */

extern	precision	dtop();		/* double to precision */
extern	double		ptod();		/* precision to double */

/*
 * vector operations
 */
pvector pvundef();			/* local variable entry */
void    pvdestroy();			/* local variable exit */
pvector pvalloc();			/* pvec allocate */
void    pvfree();			/* pvec free */
pvector pvset();			/* set each element to scaler */

#endif
