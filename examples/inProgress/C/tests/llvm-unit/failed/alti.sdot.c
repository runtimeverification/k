#include <stdio.h>
#include <altivec.h>
#include <math.h>
#include <float.h>
#define N 1027
main()
{
/* Mac G-4 sdot for arbitrary N wpp 6/8/2002 */
  float x[N] __attribute__((aligned(16)));
  float y[N] __attribute__((aligned(16)));
  float tres,res,eps;
  int flag,i,k,ki,kl,n0,n;
  static float seed = 331.0;
  float sdot(int,float *,float *);
  float ggl(float *);
  eps  = FLT_EPSILON;    /* machine eps */
  n0   = 1; kl   = 3;
  flag = 0;
  for(k=0;k<5;k++){
     for(ki=0;ki<kl;ki++){
        n    = n0 + ki;
        tres = 0.0;
        for(i=0;i<n;i++){
           x[i] = ggl(&seed);
           y[i] = ggl(&seed);
           tres = tres + x[i]*y[i];
        }
        res = sdot(n,x,y);
        if(fabs(tres-res) > ((float) n)*eps){
           flag = 1;
           printf(" n = %d, test sdot value = %e, sdot value = %e\n",
                    n,tres,res);
        }
     }
     n0 *= 4;
     kl  = 4;
  }
  if(flag == 0) printf(" All n tests passed\n");
  return 0;
}
#define NS 12
float sdot(int n, float *x, float *y)
{
  float sum,*xp,*yp;
  int i,ii,nres,nsegs;
  vector float V7 = (vector float)(0.0,0.0,0.0,0.0);
  vector float V0,V1;
  float psum[4] __attribute__((aligned(16)));
// n < NS done in scalar mode
  if(n < NS){
     sum = x[0]*y[0];
     for(i=1;i<n;i++){
        sum += x[i]*y[i];
     }
     return(sum);
  }
// n >= NS case done with altivec 
  xp = x;
  yp = y;
  V0    = vec_ld(0,xp); xp += 4;   // increment next index
  V1    = vec_ld(0,yp); yp += 4;   // increment next index
  nsegs = (n >> 2) - 1;
  nres  = n - ((nsegs+1) << 2);    // nres = n mod 4
  for(i=0;i<nsegs;i++){
     V7 = vec_madd(V0,V1,V7);       // partial sum gp. of 4
     V0 = vec_ld(0,xp); xp += 4;    // bottom load next 4 x
     V1 = vec_ld(0,yp); yp += 4;    // bottom load next 4 y
  }
  V7 = vec_madd(V0,V1,V7);          // final partial sum
// Now finish up: segment maxima are in V0, indices in V7
  vec_st(V7,0,psum);
  if(nres > 0){
     ii   = ((n >> 2) << 2);
     sum  = x[ii]*y[ii];
     ii++;
     for(i=1;i<nres;i++){
        sum += x[ii]*y[ii];
        ii++;
     }
  } else {
     sum = 0.0;
  }
  for(i=0;i<4;i++){
     sum += psum[i];
  }
  return(sum);
}
#undef NS
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
