#include <stdio.h>
#include <math.h>
#include <time.h>
#include <float.h>
#include <altivec.h>
#define N 128
#define N2 N/2
main()
{
/* SSE version of cfft2 - uses Apple intrinsics
   W. Petersen, SAM. Math. ETHZ 2 May, 2002 */
   int first,i,icase,it,n;
   int nits=1000;              /* number of iterations for timing test */
   float error,fnm1,sign,z0,z1,ggl();
   static float seed = 331.0;
   float *x,*y,*z,*w;
   float t1,ln2,mflops;
   void cffti(),cfft2();
/* allocate storage for x,y,z,w on 4-word bndr. */
   x = (float *)malloc(8*N);
   y = (float *)malloc(8*N);
   z = (float *)malloc(8*N);
   w = (float *)malloc(4*N);
   first = 1;
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
      for(it=0;it<nits;it++){
         sign = +1.0;
         cfft2(n,x,y,w,sign);
         sign = -1.0;
         cfft2(n,y,x,w,sign);
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
#define cplx __complex__ 
#define Re __real__ 
#define Im __imag__
void step
(unsigned int n,unsigned int mj, 
cplx float *a, __complex__ float *b, 
cplx float *c, __complex__ float *d, 
cplx float *w, float sign)
{
   int j,k,jc,jw,l,lj,mj2;
   float rp,up;
   float wr[4] __attribute((aligned(16))), wu[4] __attribute((aligned(16)));
   const vector float vminus = (vector float)(-0.,0.,-0.,0.);
   const vector float vzero  = (vector float)(0.,0.,0.,0.);
   const vector unsigned char pv3201 = 
   (vector unsigned char)(4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11);
   vector float v0,v1,v2,v3,v4,v5,v6,v7;

   mj2 = 2*mj;
   lj  = n/mj2;

   for(j=0; j<lj; j++){
      jw  = j*mj; jc  = j*mj2;
      rp = Re w[jw];
      up = Im w[jw];
      if(sign<0.0) up = -up;
      if(mj<2){
/* special case mj=1 */ 
         Re d[jc] = rp*(Re a[jw] - Re b[jw]) - 
                          up*(Im a[jw] - Im b[jw]);
         Im d[jc] = up*(Re a[jw] - Re b[jw]) 
                        + rp*(Im a[jw] - Im b[jw]);
         Re c[jc] = Re a[jw] + Re b[jw];
         Im c[jc] = Im a[jw] + Im b[jw];
      } else {
/* mj>=2 case */ 
         wr[0] = rp; wr[1] = rp; wr[2] = rp; wr[3] = rp; 
         wu[0] = up; wu[1] = up; wu[2] = up; wu[3] = up; 
         v6 = vec_ld(0,wr);
         v7 = vec_ld(0,wu);
         v7 = vec_xor(v7,vminus);
         for(k=0; k<mj; k+=2){
            v0 = vec_ld(0,(vector float *) &a[jw+k]); /* read a */
            v1 = vec_ld(0,(vector float *) &b[jw+k]); /* read b */
            v2 = vec_add(v0, v1);
            vec_st(v2,0,(vector float *) &c[jc+k]);   /* store c */
            v3 = vec_sub(v0, v1); 
            v4 = vec_perm(v3,v3,pv3201);
            v0 = vec_madd(v6,v3,vzero);
            v1 = vec_madd(v7,v4,vzero);
            v2 = vec_add(v0,v1);                     /* w*(a - b) */
            vec_st(v2,0,(vector float *) &d[jc+k]);  /* store a */
         }
      }
   }
}
#undef cplx 
#undef Re 
#undef Im
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
