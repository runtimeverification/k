#include <stdio.h>
#include <math.h>
#include <time.h>
#include <float.h>
#include "xmmintrin.h"
#define N 1024
#define N2 N/2

/* allocate storage for x,y,z,w on 4-word bndr. */
float x[2*N] __attribute__ ((aligned (16)));
float y[2*N] __attribute__ ((aligned (16)));
float z[2*N] __attribute__ ((aligned (16)));
float w[  N] __attribute__ ((aligned (16)));

int main()
{
/* 
   SSE version of cfft2 - uses Intel intrinsics.
   Expanded version 
   
              wpp, SAM. Math. ETHZ 21 May, 2002 
*/
   int first,i,icase,it,n;
   double error;
   float fnm1,seed,sign,z0,z1,ggl();
   float t1,ln2,mflops;
   void cffti(),cfft2();

   first = 1;
   seed  = 331.0;
   for(icase=0;icase<2;icase++){
   if(first){
      for(i=0;i<2*N;i+=2){
         z0 = ggl(&seed);     /* real part of array */
         z1 = ggl(&seed);     /* imaginary part of array */
         x[i] = z0;
         z[i] = z0;           /* copy of initial real data */
         x[i+1] = z1;
         z[i+1] = z1;         /* copy of initial imag. data */
      }
   } else {
      for(i=0;i<2*N;i+=2){
         z0 = 0;              /* real part of array */
         z1 = 0;              /* imaginary part of array */
         x[i] = z0;
         z[i] = z0;           /* copy of initial real data */
         x[i+1] = z1;
         z[i+1] = z1;         /* copy of initial imag. data */
      }
   }
/* initialize sine/cosine tables */
   n = N;
   cffti(n,w);
/* transform forward, back */
   if(first){
      sign = 1.0;
      cfft2(n,x,y,w,sign);
      sign = -1.0;
      cfft2(n,y,x,w,sign);
/* results should be same as initial multiplied by N */
      fnm1 = 1.0/((float) n);
      error = 0.0;
      for(i=0;i<2*N;i+=2){
         error += (z[i] - fnm1*x[i])*(z[i] - fnm1*x[i]) +
                (z[i+1] - fnm1*x[i+1])*(z[i+1] - fnm1*x[i+1]);
      }
      error = sqrt(fnm1*error);
      printf(" for n=%d, fwd/bck error=%e\n",N,error);
      first = 0;
   } else {
      unsigned j = 0;
      for(it=0;it<20000;it++){
         sign = +1.0;
         cfft2(n,x,y,w,sign);
         sign = -1.0;
         cfft2(n,y,x,w,sign);
      }
      printf(" for n=%d\n",n);
      for (i = 0; i<N; ++i) {
        printf("%g  ", w[i]);
        j++;
        if (j == 4) {
          printf("\n");
          j = 0;
        }
      }
   }
   }
   return 0;
}
void cfft2(n,x,y,w,sign)
int n;
float x[][2],y[][2],w[][2],sign;
{
   int jb, jc, jw, k, k2, lj, m, j, mj, mj2, pass, tgle;
   float (*a)[2],(*b)[2],(*c)[2],(*d)[2];
   float (*aa)[2],(*bb)[2],(*cb)[2],(*dd)[2];
   float rp,up;
   float wr[4] __attribute__ ((aligned (16)));
   float wu[4] __attribute__ ((aligned (16)));
   __m128 V0,V1,V2,V3,V4,V5,V6,V7;
   __m128 V8,V9,V10,V11,V12,V13,V14,V15;

   if(n<=1){
      y[0][0] = x[0][0];
      y[0][1] = x[0][1];
      return;
   }
   m    = (int) (log((float) n)/log(1.99));
   mj   = 1;
   mj2  = 2;
   lj   = n/2;
// first pass thru data: x -> y
   a = (void *)&x[0][0];
   b = (void *)&x[n/2][0];
   c = (void *)&y[0][0];
   d = (void *)&y[1][0];
   for(j=0;j<lj;j++){
      jc  = j*mj2;
      rp = w[j][0]; up = w[j][1];
      if(sign<0.0) up = -up;
      d[jc][0] = rp*(a[j][0] - b[j][0]) - up*(a[j][1] - b[j][1]);
      d[jc][1] = up*(a[j][0] - b[j][0]) + rp*(a[j][1] - b[j][1]);
      c[jc][0] = a[j][0] + b[j][0];
      c[jc][1] = a[j][1] + b[j][1];
   }
   if(n==2) return;
// next pass is mj = 2
   mj  = 2;
   mj2 = 4;
   lj  = n/4;
   a = (void *)&y[0][0];
   b = (void *)&y[n/2][0];
   c = (void *)&x[0][0];
   d = (void *)&x[mj][0];
   if(n==4){
      c = (void *)&y[0][0];
      d = (void *)&y[mj][0];
   }
   for(j=0;j<lj;j++){
      jw = j*mj; jc = j*mj2;
      rp = w[jw][0]; up = w[jw][1];
      if(sign<0.0) up = -up;
      wr[0] =  rp; wr[1] = rp; wr[2] =  rp; wr[3] = rp;
      wu[0] = -up; wu[1] = up; wu[2] = -up; wu[3] = up;
      V6 = _mm_load_ps(wr);
      V7 = _mm_load_ps(wu);
      V0 = _mm_load_ps(&a[jw][0]);
      V1 = _mm_load_ps(&b[jw][0]);
      V2 = _mm_add_ps(V0,V1);            /* a + b */
      _mm_store_ps(&c[jc][0],V2);          /* store c */
      V3 = _mm_sub_ps(V0,V1);            /* a - b */
      V4 = _mm_shuffle_ps(V3,V3,_MM_SHUFFLE(2,3,0,1));
      V0 = _mm_mul_ps(V6,V3);
      V1 = _mm_mul_ps(V7,V4);
      V2 = _mm_add_ps(V0,V1);            /* w*(a - b) */
      _mm_store_ps(&d[jc][0],V2);          /* store d */
   }
   if(n==4) return;
   mj  *= 2;
   mj2  = 2*mj;
   lj   = n/mj2; 
   tgle = 0;  
   for(pass=2;pass<m-1;pass++){
      if(tgle){
         a = (void *)&y[0][0];
         b = (void *)&y[n/2][0];
         c = (void *)&x[0][0];
         d = (void *)&x[mj][0];
 	 tgle = 0;
      } else {
         a = (void *)&x[0][0];
         b = (void *)&x[n/2][0];
         c = (void *)&y[0][0];
         d = (void *)&y[mj][0];
	 tgle = 1;
      }
      for(j=0; j<lj; j++){
         jw = j*mj; jc = j*mj2;
         rp = w[jw][0];
         up = w[jw][1];
         if(sign<0.0) up = -up;
         wr[0] =  rp; wr[1] = rp; wr[2] =  rp; wr[3] = rp;
         wu[0] = -up; wu[1] = up; wu[2] = -up; wu[3] = up;
         V6 = _mm_load_ps(wr);
         V7 = _mm_load_ps(wu);
         for(k=0; k<mj; k+=4){
            k2   = k + 2;
            V0 = _mm_load_ps(&a[jw+k][0]);
            V1 = _mm_load_ps(&b[jw+k][0]);
            V2 = _mm_add_ps(V0,V1);            /* a + b */
            _mm_store_ps(&c[jc+k][0],V2);      /* store c */
            V3 = _mm_sub_ps(V0,V1);            /* a - b */
            V4 = _mm_shuffle_ps(V3,V3,_MM_SHUFFLE(2,3,0,1));
            V0 = _mm_mul_ps(V6,V3);
            V1 = _mm_mul_ps(V7,V4);
            V2 = _mm_add_ps(V0,V1);            /* w*(a - b) */
            _mm_store_ps(&d[jc+k][0],V2);      /* store d */
	    V8 = _mm_load_ps(&a[jw+k2][0]);
	    V9 = _mm_load_ps(&b[jw+k2][0]);
	    V10 = _mm_add_ps(V8,V9);		/* a + b */
	    _mm_store_ps(&c[jc+k2][0],V10);     /* store c */
	    V11 = _mm_sub_ps(V8,V9);		/* a - b */
	    V12 = _mm_shuffle_ps(V11,V11,_MM_SHUFFLE(2,3,0,1));
	    V8  = _mm_mul_ps(V6,V11);
	    V9  = _mm_mul_ps(V7,V12);
	    V10 = _mm_add_ps(V8,V9);		/* w*(a - b) */
	    _mm_store_ps(&d[jc+k2][0],V10);	/* store d */
         }
      }
      mj  *= 2;
      mj2  = 2*mj;
      lj   = n/mj2;
   }
/* last pass thru data: in-place if previous in y */
   c = (void *)&y[0][0];
   d = (void *)&y[n/2][0];
   if(tgle) {
      a = (void *)&y[0][0];
      b = (void *)&y[n/2][0];
   } else {
      a = (void *)&x[0][0];
      b = (void *)&x[n/2][0];
   }
   for(k=0; k<(n/2); k+=4){
      k2   = k + 2;
      V0 = _mm_load_ps(&a[k][0]);
      V1 = _mm_load_ps(&b[k][0]);
      V2 = _mm_add_ps(V0,V1);         /* a + b */
      _mm_store_ps(&c[k][0],V2);      /* store c */
      V3 = _mm_sub_ps(V0,V1);         /* a - b */
      _mm_store_ps(&d[k][0],V3);      /* store d */
      V4 = _mm_load_ps(&a[k2][0]);
      V5 = _mm_load_ps(&b[k2][0]);
      V6 = _mm_add_ps(V4,V5);         /* a + b */
      _mm_store_ps(&c[k2][0],V6);     /* store c */
      V7 = _mm_sub_ps(V4,V5);         /* a - b */
      _mm_store_ps(&d[k2][0],V7);     /* store d */
   }
}
void cffti(int n, float w[][2])
{
   int i,n2;
   float aw,arg,pi;
   pi = 3.141592653589793;
   n2 = n/2;
   aw = 2.0*pi/((float)n);
#pragma vector
   for(i=0;i<n2;i++){
      arg   = aw*((float)i);
      w[i][0] = cos(arg);
      w[i][1] = sin(arg);
   }
}
#include <math.h>
float ggl(float *ds)
{
/* generate u(0,1) distributed random numbers.
   Seed ds must be saved between calls. ggl is
   essentially the same as the IMSL routine RNUM.
                                                                                
   W. Petersen and M. Troyer, 24 Oct. 2002, ETHZ:
   a modification of a fortran version from
   I. Vattulainen, Tampere Univ. of Technology,
   Finland, 1992 */
                                                                                
   double t,d2=0.2147483647e10;
   t   = (float) *ds;
   t   = fmod(0.16807e5*t,d2);
   *ds = (float) t;
   return((float) ((t-1.0e0)/(d2-1.0e0)));
}
