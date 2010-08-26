#include "pdefs.h"
#include "precision.h"

#ifdef DEBUG
#include <stdio.h>
#endif

#ifdef ASM_16BIT
#include "asm16bit.h"
#endif

/*
 *   Divide u (dividend) by v (divisor); If non-null, qp and rp are set to
 *   quotient and remainder.  The result returned will be *qp, unless qp is
 *   NULL, then *rp will be returned if non-null, otherwise pUndef is returned.
 *
 *  Produce:
 * 
 *	 q (quotient)	= u div v	(v != 0)
 *			  truncation is toward zero
 *	
 *	 r (remainder)	= u mod v
 *			= u - u div v * v      (v != 0)
 *			= u		       (v == 0)
 *			  ( e.g.  u == q*v + r )
 *			remainder has same sign and dividend
 *
 * Note: this has opposite convention than the C standard div fuction,
 *	 but the same convention of the typical C "/" operator
 *	 It is also inconvienient for the mod function.	 
 */
/*
 *	This algorithm is taken almost verbatum from Knuth Vol 2.
 *	Please note the following trivial(?) array index
 *	transformations (since MSD to LSD order is reversed):
 *	
 *	q[0..m] to Q[0..m]   thus   q[i] == Q[m-i]
 *	r[1..n]	   R[0..n-1]	    r[i] == R[n+1-i]
 *	u[0..m+n]  w[0..m+n]	    u[i] == w[m+n-i]
 *	v[1..n]	   x[0..n-1]	    v[i] == x[n-i]
 *	
 *	let N == n - 1 so that n == N + 1 thus:
 *	
 *	q[0..m] to Q[0..m]   thus   q[i] == Q[m-i]
 *	r[1..n]	   R[0..N]	    r[i] == R[N+2-i]
 *	u[0..m+n]  w[0..m+N+1]	    u[i] == w[m+N+1-i]
 *	v[1..n]	   x[0..N]	    v[i] == x[N+1-i]
 */

/*
 * Note: Be very observent of the usage of uPtr, and vPtr.
 *       They are used to point to u, v, w, q or r as necessary.
 */
precision pdivmod(u, v, qp, rp)
   precision u, v, *qp, *rp;
{
   register digitPtr	uPtr, vPtr, qPtr, LastPtr;

   register accumulator temp;		       /* 0 <= temp < base^2 */
   register digit	carry;			   /* 0 <= carry < 2 */
   register digit	hi;			   /* 0 <= hi < base */

   register posit	n, m;
   digit		d;			    /* 0 <= d < base */
   digit		qd;			   /* 0 <= qd < base */
#ifdef DEBUG
   int			i;
#endif

   precision		q, r, w;   /* quotient, remainder, temporary */

   n = v->size;					  /* size of v and r */

   (void) pparm(u);
   (void) pparm(v);
   if (u->size < n) {
      q = pUndef;
      r = pUndef;
      pset(&q, pzero);
      pset(&r, u);
      goto done;
   }

   m = u->size - n;

   uPtr = u->value + m + n;
   vPtr = v->value + n;

   q = palloc(m + 1);
   if (q == pUndef) return q;

   q->sign = (u->sign != v->sign);		  /* can generate -0 */

   r = palloc(n);
   if (r == pUndef) {
      pdestroy(q);
      return r;
   }
   r->sign = u->sign;	    
/* 
 * watch out! does this function return: q=floor(a/b) or trunc(a/b)?
 * it's currently the latter, but every mathmaticion I have talked to
 * prefers the former so that a % b returns between 0 to b-1.  The
 * problem is that this is slower and disagrees with C common practice.
 */
   qPtr = q->value + m + 1;

   if (n == 1) {
      d = *--vPtr;			     /* d is only digit of v */
      if (d == 0) {				  /* divide by zero? */
	 q = pnew(errorp(PDOMAIN, "pdivmod", "divide by zero"));
      } else {				      /* single digit divide */
#ifndef ASM_16BIT
	 vPtr = r->value + n;
	 hi = 0;			  /* hi is current remainder */
	 do {
	     temp    = mulBase(hi);	/* 0 <= temp <= (base-1)^2   */
	     temp   += *--uPtr;		/* 0 <= temp <= base(base-1) */
	     hi	     = uModDiv(temp, d, --qPtr); /* 0 <= hi < base */
	 } while (uPtr > u->value);
	 *--vPtr = hi;
#else
	qPtr -= m + 1;
	*(r->value) = memdivw1(qPtr, u->value, m + 1, d);
#endif
      }					  
   } else {					/* muti digit divide */
      /*
       * normalize:   multiply u and v by d so hi digit of v > b/2 
       */
      d = BASE / (*--vPtr+1);			  /* high digit of v */

      w = palloc(n);					/* size of v */
      if (w == pUndef) return w;

#ifndef ASM_16BIT
      vPtr = v->value;
      uPtr = w->value;		    /* very confusing.	just a temp */
      LastPtr = vPtr + n;
      hi = 0;
      do {				    /* single digit multiply */
	 temp	 = uMul(*vPtr++, d);   /* 0<= temp <= base(base-1)/2 */
	 temp	+= hi;			/* 0 <= temp <= (base^2-1)/2 */
	 hi	 = divBase(temp);	     /* 0 <= hi	  < base / 2 */
	 *uPtr++ = modBase(temp);	     /* 0 <= hi	  < base / 2 */
      } while (vPtr < LastPtr);			  /* on exit hi == 0 */
#else
      hi = memmulw1(w->value, v->value, n, d);
#endif

      pset(&v, w);
      pdestroy(w);

      w = palloc(m + n + 1);
      if (w == pUndef) return w;

#ifndef ASM_16BIT
      uPtr = u->value;
      vPtr = w->value;		     /* very confusing.	 just a temp */
      LastPtr = uPtr + m + n;
      do {				    /* single digit multiply */
	 temp	 = uMul(*uPtr++, d);	      
	 temp	+= hi;	      
	 hi	 = divBase(temp);
	 *vPtr++ = modBase(temp);
      } while (uPtr < LastPtr);
      *vPtr = hi;				 /* note extra digit */
#else
      hi = memmulw1(w->value, u->value, m + n, d);
      w->value[m + n] = hi;
#endif

      pset(&u, w);
      pdestroy(w);

#ifdef DEBUG
      printf("m = %d    n = %d\nd = %d\n", m, n, d);
      printf("norm u = "); pshow(u);
      printf("norm v = "); pshow(v);
#endif

      uPtr = u->value + m + 1;		  /* current least significant digit */
      do {
	 --uPtr;
#ifdef DEBUG
	 printf("   u = ");
	 for (i = n; i >= 0; --i) printf("%.*x ", sizeof(digit) * 2, uPtr[i]);
	 putchar('\n');
	 printf("   v = "); 
	 for (i = 1; i < 3; i++) printf("%.*x ", sizeof(digit) * 2, 
	    v->value[n-i]);
	 putchar('\n');
#endif
#ifndef ASM_16BIT
	 vPtr    = v->value + n;
	 LastPtr = uPtr + n;
	 if (*LastPtr == *--vPtr) {			 /* guess next digit */
	    qd = BASE - 1;
	 } else {
	    temp  = mulBase(*LastPtr);
	    temp += *--LastPtr;				/* 0 <= temp< base^2 */
	    temp  = uModDiv(temp, *vPtr, &qd);
	    --vPtr;
	    --LastPtr;
	    while (uMul(*vPtr, qd) > mulBase(temp) + *LastPtr) {
	       --qd;
	       temp += vPtr[1];
	       if (temp >= BASE) break;  /* if so, vPtr*qd <= temp*base */
	    }		
	    LastPtr += 2;
	 }
	 /*
	  * Single digit Multiply then Subtract
	  */
	 vPtr  = v->value;
	 carry = 1;			 /* noborrow bit */
	 hi    = 0;			 /* hi digit of multiply */
	 do {
	    /* multiply */
	    temp    = uMul(qd, *vPtr++); /* 0 <= temp <= (base-1)^2   */
	    temp   += hi;		 /* 0 <= temp <= base(base-1) */
	    hi	    = divBase(temp);
	    temp    = modBase(temp);
	    /* subtract */
	    temp    = (BASE-1) - temp;	 /* 0 <= temp < base */
	    temp   += *uPtr + carry;	 /* 0 <= temp < 2*base */
	    carry   = divBase(temp);
	    *uPtr++ = modBase(temp);	 /* 0 <= carry < 2 */
	 } while (uPtr < LastPtr);
	 temp  = (BASE-1) - hi;
	 temp += *uPtr + carry;
	 carry = divBase(temp);
	 *uPtr = modBase(temp);
	 uPtr -= n;
#else
#if 0
	 carry = !memmulsubw(uPtr, v->value, n, qd); 	/* 1 if noborrow */
#endif
	 carry = !memdivw(uPtr, v->value, n, &qd); 	/* 1 if noborrow */
#endif
#ifdef DEBUG
	 printf("   qhat = %.*x\n", sizeof(digit) * 2, qd);
	 printf("   new u = "); 
	 for (i = n; i >= 0; --i) printf("%.*x ", sizeof(digit) * 2, uPtr[i]);
	 putchar('\n');
#endif
	 if (carry == 0) {		 /* Test remainder, add back */
	    vPtr    = v->value;
	    LastPtr = uPtr + n;
	    do {
	       temp    = *uPtr + *vPtr++;
	       temp   += carry;
	       carry   = divBase(temp);
	       *uPtr++ = modBase(temp);
	    } while (uPtr < LastPtr);
	    *uPtr += carry - BASE;	   /* real strange but works */
	    uPtr -= n;
	    --qd;
#ifdef DEBUG
	    printf("   decrementing q...adding back\n");
	    printf("   fixed u = "); 
	    for (i = n; i >= 0; --i) printf("%.*x ", sizeof(digit) * 2, uPtr[i]);
	    putchar('\n');
	    printf("   newq = %.*x\n", sizeof(digit) * 2, qd);
#endif
	 }
	 *--qPtr = qd;			/* one leading zero possible */
#ifdef DEBUG
	 putchar('\n'); 
#endif
      } while (uPtr > u->value);

      /*
       * Un-normalize to get remainder
       */
#ifndef ASM_16BIT
      uPtr = u->value + n;		/* skip hi digit (it's zero) */
      vPtr = r->value + n;
      hi   = 0;				/* hi is current remainder   */
      do {				/* single digit divide	     */
	  temp	  = mulBase(hi);	/* 0<=temp < base^2-(base-1) */
	  temp	 += *--uPtr;		/* 0 <= temp < base^2	     */
	  hi	  = uModDiv(temp, d, --vPtr);
      } while (uPtr > u->value);	/* carry will be zero	     */
#else 
      carry = memdivw1(r->value, u->value, n, d); 	 /* always 0 */
#endif
      pnorm(r);		      /* remainder may have many leading 0's */
   }

   if (m > 0 && qPtr[m] == 0) {
      --(q->size);					 /* normalize */
   }
   if (q->size == 1 && *qPtr == 0) q->sign = false;

done:

   pdestroy(u);
   pdestroy(v);

   if (rp == (precision *) -1) {
      if (qp != pNull) pset(qp, q);
      pdestroy(q);
      return presult(r);
   } else if (qp == (precision *) -1) {
      if (rp != pNull) pset(rp, r);
      pdestroy(r);
      return presult(q);
   }
   if (qp != pNull) pset(qp, q);
   if (rp != pNull) pset(rp, r);
   pdestroy(q);
   pdestroy(r);
   return pUndef;
}
