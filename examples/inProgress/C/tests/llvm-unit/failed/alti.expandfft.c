#include <stdio.h>
#include <math.h>
#include <time.h>
#include <float.h>
#include <stdlib.h>
#include <altivec.h>
#define N 1048576
#define N2 N/2
void cfft2(unsigned int n,float x[][2],float y[][2],float w[][2], float sign);
void cffti(int n, float w[][2]);

main()
{
/* 
   Example of Apple Altivec coded binary radix FFT
   using intrinsics from Petersen and Arbenz "Intro. 
   to Parallel Computing," Section 3.6
 
   This is an expanded version of a generic work-space 
   FFT: steps are in-line. cfft2(n,x,y,w,sign) takes complex
   n-array "x" (Fortran real,aimag,real,aimag,... order) 
   and writes its DFT in "y". Both input "x" and the 
   original contents of "y" are destroyed. Initialization
   for array "w" (size n/2 complex of twiddle factors
   (exp(twopi*i*k/n), for k=0..n/2-1)) is computed once
   by cffti(n,w).

                      WPP, SAM. Math. ETHZ, 1 June, 2002 
*/

   int first,i,icase,it,ln2,n;
   int nits=1000000;
   static float seed = 331.0;
   float error,fnm1,sign,z0,z1,ggl();
   float *x,*y,*z,*w;
   double t1,mflops;
/* allocate storage for x,y,z,w on 4-word bndr. */
   x = (float *) malloc(8*N);
   y = (float *) malloc(8*N);
   z = (float *) malloc(8*N);
   w = (float *) malloc(4*N);
   n     = 2;
   for(ln2=1;ln2<21;ln2++){
      first = 1;
      for(icase=0;icase<2;icase++){
         if(first){
            for(i=0;i<2*n;i+=2){
               z0 = ggl(&seed);     /* real part of array */
               z1 = ggl(&seed);     /* imaginary part of array */
               x[i] = z0;
               z[i] = z0;           /* copy of initial real data */
               x[i+1] = z1;
               z[i+1] = z1;         /* copy of initial imag. data */
            }
         } else {
            for(i=0;i<2*n;i+=2){
               z0 = 0;              /* real part of array */
               z1 = 0;              /* imaginary part of array */
               x[i] = z0;
               z[i] = z0;           /* copy of initial real data */
               x[i+1] = z1;
               z[i+1] = z1;         /* copy of initial imag. data */
            }
         }
/* initialize sine/cosine tables */
         cffti(n,w);
/* transform forward, back */
         if(first){
            sign = 1.0;
            cfft2(n,x,y,w,sign);
            sign = -1.0;
            cfft2(n,y,x,w,sign);
/* results should be same as initial multiplied by n */
            fnm1 = 1.0/((float) n);
            error = 0.0;
            for(i=0;i<2*n;i+=2){
               error += (z[i] - fnm1*x[i])*(z[i] - fnm1*x[i]) +
                   (z[i+1] - fnm1*x[i+1])*(z[i+1] - fnm1*x[i+1]);
            }
            error = sqrt(fnm1*error);
            printf(" for n=%d, fwd/bck error=%e\n",n,error);
            first = 0;
         } else {
            for(it=0;it<nits;it++){
               sign = +1.0;
               cfft2(n,x,y,w,sign);
               sign = -1.0;
               cfft2(n,y,x,w,sign);
            }
         }
      }
      if((ln2%4)==0) nits /= 10;
      n *= 2;
   }
 return 0;
}
void cfft2(unsigned int n,float x[][2],float y[][2],float w[][2], float sign)
{

/* 
   altivec version of cfft2 from Petersen and Arbenz book, "Intro.
   to Parallel Computing", Oxford Univ. Press, 2003, Section 3.6
                                        wpp 14. Dec. 2003
*/

   int jb,jc,jd,jw,k,k2,k4,lj,m,j,mj,mj2,pass,tgle;
   float rp,up,wr[4] __attribute((aligned(16)));
   float wu[4] __attribute((aligned(16)));
   float *a,*b,*c,*d;
   const vector float vminus = (vector float)(-0.,0.,-0.,0.);
   const vector float vzero  = (vector float)(0.,0.,0.,0.);
   const vector unsigned char pv3201 =
   (vector unsigned char)(4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11);
   vector float V0,V1,V2,V3,V4,V5,V6,V7;
   vector float V8,V9,V10,V11,V12,V13,V14,V15;

   if(n<=1){
      y[0][0] = x[0][0];
      y[0][1] = x[0][1];
      return;
   }
   m    = (int) (log((float) n)/log(1.99));
   mj   = 1;
   mj2  = 2;
   lj   = n/2;
/* first pass thru data: x -> y */
   for(j=0;j<lj;j++){
      jb = n/2+j; jc  = j*mj2; jd = jc + 1;
      rp = w[j][0]; up = w[j][1];
      if(sign<0.0) up = -up;
      y[jd][0] = rp*(x[j][0] - x[jb][0]) - up*(x[j][1] - x[jb][1]);
      y[jd][1] = up*(x[j][0] - x[jb][0]) + rp*(x[j][1] - x[jb][1]);
      y[jc][0] = x[j][0] + x[jb][0];
      y[jc][1] = x[j][1] + x[jb][1];
   }
   if(n==2) return;
/* next pass is mj = 2 */
   mj  = 2;
   mj2 = 4;
   lj  = n/4;
   a = (float *)&y[0][0];
   b = (float *)&y[n/2][0];
   c = (float *)&x[0][0];
   d = (float *)&x[mj][0];
   if(n==4){
      c = (float *)&y[0][0];
      d = (float *)&y[mj][0];
   }
   for(j=0;j<lj;j++){
      jw = j*mj; jc = j*mj2; jd = 2*jc;
      rp = w[jw][0]; up = w[jw][1];
      if(sign<0.0) up = -up;
      wr[0] = rp; wr[1] = rp; wr[2] = rp; wr[3] = rp;
      wu[0] = up; wu[1] = up; wu[2] = up; wu[3] = up;
      V6 = vec_ld(0,wr);
      V7 = vec_ld(0,wu);
      V7 = vec_xor(V7,vminus);
      V0 = vec_ld(0,(vector float *) (a+jc));
      V1 = vec_ld(0,(vector float *) (b+jc));
      V2 = vec_add(V0,V1);                         /* a + b */
      vec_st(V2,0,(vector float *) (c+jd));     /* store c */
      V3 = vec_sub(V0,V1);                         /* a - b */
      V4 = vec_perm(V3,V3,pv3201);
      V0 = vec_madd(V6,V3,vzero);
      V1 = vec_madd(V7,V4,vzero);
      V2 = vec_add(V0,V1);                         /* w*(a - b) */
      vec_st(V2,0,(vector float*) (d+jd));         /* store d */
   }
   if(n==4) return;
   mj  *= 2;
   mj2  = 2*mj;
   lj   = n/mj2; 
   tgle = 0;  
   for(pass=2;pass<m-1;pass++){
      if(tgle){
         a = (float *)&y[0][0];
         b = (float *)&y[n/2][0];
         c = (float *)&x[0][0];
         d = (float *)&x[mj][0];
 	 tgle = 0;
      } else {
         a = (float *)&x[0][0];
         b = (float *)&x[n/2][0];
         c = (float *)&y[0][0];
         d = (float *)&y[mj][0];
	 tgle = 1;
      }
      for(j=0; j<lj; j++){
         jw = j*mj; jc = j*mj2; jd = 2*jc;
         rp = w[jw][0];
         up = w[jw][1];
         if(sign<0.0) up = -up;
         wr[0] = rp; wr[1] = rp; wr[2] = rp; wr[3] = rp;
         wu[0] = up; wu[1] = up; wu[2] = up; wu[3] = up;
         V6 = vec_ld(0,wr);
         V7 = vec_ld(0,wu);
         V7 = vec_xor(V7,vminus);
         for(k=0; k<mj; k+=4){
            k2   = 2*k; k4 = k2+4;
            V0 = vec_ld(0,(vector float *) (a+jc+k2));
            V1 = vec_ld(0,(vector float *) (b+jc+k2));
            V2 = vec_add(V0,V1);                        /* a + b */
            vec_st(V2,0,(vector float*) (c+jd+k2));   /* store c */
            V3 = vec_sub(V0,V1);                        /* a - b */
            V4 = vec_perm(V3,V3,pv3201);
            V0 = vec_madd(V6,V3,vzero);
            V1 = vec_madd(V7,V4,vzero);
            V2 = vec_add(V0,V1);                        /* w*(a - b) */
            vec_st(V2,0,(vector float *) (d+jd+k2));    /* store d */
	    V8 = vec_ld(0,(vector float *) (a+jc+k4));
	    V9 = vec_ld(0,(vector float *) (b+jc+k4));
	    V10 = vec_add(V8,V9);		        /* a + b */
	    vec_st(V10,0,(vector float *) (c+jd+k4));   /* store c */
	    V11 = vec_sub(V8,V9);		        /* a - b */
	    V12 = vec_perm(V11,V11,pv3201);
	    V8  = vec_madd(V6,V11,vzero);
	    V9  = vec_madd(V7,V12,vzero);
	    V10 = vec_add(V8,V9);		        /* w*(a - b) */
	    vec_st(V10,0,(vector float *) (d+jd+k4));   /* store d */
         }
      }
      mj  *= 2;
      mj2  = 2*mj;
      lj   = n/mj2;
   }
/* last pass thru data: in-place if previous in y */
   c = (float *)&y[0][0];
   d = (float *)&y[n/2][0];
   if(tgle) {
      a = (float *)&y[0][0];
      b = (float *)&y[n/2][0];
   } else {
      a = (float *)&x[0][0];
      b = (float *)&x[n/2][0];
   }
   for(k=0; k<(n/2); k+=4){
      k2 = 2*k; k4 = k2+4;
      V0 = vec_ld(0,(vector float *) (a+k2));
      V1 = vec_ld(0,(vector float *) (b+k2));
      V2 = vec_add(V0,V1);                      /* a + b */
      vec_st(V2,0,(vector float*) (c+k2));      /* store c */
      V3 = vec_sub(V0,V1);                      /* a - b */
      vec_st(V3,0,(vector float *) (d+k2));     /* store d */
      V4 = vec_ld(0,(vector float *) (a+k4));
      V5 = vec_ld(0,(vector float *) (b+k4));
      V6 = vec_add(V4,V5);                      /* a + b */
      vec_st(V6,0,(vector float *) (c+k4));     /* store c */
      V7 = vec_sub(V4,V5);                      /* a - b */
      vec_st(V7,0,(vector float *) (d+k4));     /* store d */
   }
}
void cffti(int n, float w[][2])
{

/* initialization routine for cfft2: computes
        cos(twopi*k),sin(twopi*k) for k=0..n/2-1
   - the "twiddle factors" for a binary radix FFT */

   int i,n2;
   float aw,arg,pi;
   pi = 3.141592653589793;
   n2 = n/2;
   aw = 2.0*pi/((float)n);
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
