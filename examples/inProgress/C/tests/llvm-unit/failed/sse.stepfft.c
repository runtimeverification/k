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
   SSE version of cfft2 - uses INTEL intrinsics
       W. Petersen, SAM. Math. ETHZ 2 May, 2002 
*/
   int first,i,icase,it,n;
   float seed,error,fnm1,sign,z0,z1,ggl();
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
   int jb, m, j, mj, tgle;
   void ccopy(),step();
   m    = (int) (log((float) n)/log(1.99));
   mj   = 1;
   tgle = 1;  /* toggling switch for work array */
   step(n,mj,&x[0][0],&x[n/2][0],&y[0][0],&y[mj][0],w,sign);
   for(j=0;j<m-2;j++){
      mj *= 2;
      if(tgle){
         step(n,mj,&y[0][0],&y[n/2][0],&x[0][0],&x[mj][0],w,sign);
         tgle = 0;
      } else {
         step(n,mj,&x[0][0],&x[n/2][0],&y[0][0],&y[mj][0],w,sign);
         tgle = 1;
      }
   }
/* last pass thru data: move y to x if needed */
   if(tgle) {
      ccopy(n,y,x);
   }
   mj   = n/2;
   step(n,mj,&x[0][0],&x[n/2][0],&y[0][0],&y[mj][0],w,sign);
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
void ccopy(int n, float x[][2], float y[][2])
{
   int i;
   for(i=0;i<n;i++){
      y[i][0] = x[i][0];
      y[i][1] = x[i][1];
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
void step(n,mj,a,b,c,d,w,sign)
int n, mj; 
float a[][2],b[][2],c[][2],d[][2],w[][2],sign;
{
   int j,k,jc,jw,l,lj,mj2,mseg;
   float rp,up;
   float wr[4] __attribute__ ((aligned (16)));
   float wu[4] __attribute__ ((aligned (16)));
   __m128 xmm0,xmm1,xmm2,xmm3,xmm4,xmm5,xmm6,xmm7;

   mj2 = 2*mj;
   lj  = n/mj2;

   for(j=0; j<lj; j++){
      jw  = j*mj; jc  = j*mj2;
      rp = w[jw][0];
      up = w[jw][1];
      if(sign<0.0) up = -up;
      if(mj<2){
/* special case mj=1 */ 
         d[jc][0] = rp*(a[jw][0] - b[jw][0]) - up*(a[jw][1] - b[jw][1]);
         d[jc][1] = up*(a[jw][0] - b[jw][0]) + rp*(a[jw][1] - b[jw][1]);
         c[jc][0] = a[jw][0] + b[jw][0];
         c[jc][1] = a[jw][1] + b[jw][1];
      } else {
/* mj>=2 case */ 
/*       _mm_prefetch((char *)&a[jw][0],_MM_HINT_NTA); */
/*       _mm_prefetch((char *)&b[jw][0],_MM_HINT_NTA); */
         wr[0] =  rp; wr[1] = rp; wr[2] =  rp; wr[3] = rp;
         wu[0] = -up; wu[1] = up; wu[2] = -up; wu[3] = up;
         xmm6 = _mm_load_ps(wr);
         xmm7 = _mm_load_ps(wu);
         for(k=0; k<mj; k+=2){
/*          _mm_prefetch((char *)&a[jw+k][0],_MM_HINT_NTA); */
/*          _mm_prefetch((char *)&b[jw+k][0],_MM_HINT_NTA); */
            xmm0 = _mm_load_ps(&a[jw+k][0]);
            xmm1 = _mm_load_ps(&b[jw+k][0]);
            xmm2 = _mm_add_ps(xmm0,xmm1);            /* a + b */
            _mm_store_ps(&c[jc+k][0],xmm2);          /* store c */
            xmm3 = _mm_sub_ps(xmm0,xmm1);            /* a - b */
            xmm4 = _mm_shuffle_ps(xmm3,xmm3,_MM_SHUFFLE(2,3,0,1));   
            xmm0 = _mm_mul_ps(xmm6,xmm3);   
            xmm1 = _mm_mul_ps(xmm7,xmm4);   
            xmm2 = _mm_add_ps(xmm0,xmm1);            /* w*(a - b) */
            _mm_store_ps(&d[jc+k][0],xmm2);          /* store d */
         }
      }
   }
}
