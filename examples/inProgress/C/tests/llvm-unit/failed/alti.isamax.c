#include <stdio.h>
#include <math.h>
#include <float.h>
#include <altivec.h>
#define N 1028
main()
{
/* 
  Mac G-4 unit step isamax for arbitrary N code 
  This is an Altivec version of isamax0 from Section 3.5.7
  in Arbenz and Petersen, "Intro. to Parallel Computing"
  Oxford Univ. Press, 2004
                                           wpp 5/8/2002 
*/
  float x[N] __attribute__((aligned(16)));
  float xb;
  int err,flag,i,im,k,ki,kl,ib,n0,n;
  int isamax(int,float *);
  static float seed = 331.0;
  float ggl(float*);
  flag = 0;                         // error flag
  kl   = 3;
  n0   = 1;
  for(k=0;k<5;k++){
     for(ki=0;ki<kl;ki++){
        n  = n0 + ki;
        ib = 0; xb = 0.0;
        for(i=0;i<n;i++){
           x[i] = ggl(&seed);
           if(fabs(x[i]) > xb){
              xb = fabs(x[i]);
              ib = i;
           }
        }
        im  = isamax(n,x);
        err = ib - im;
        if(err != 0){
            printf(" err in isamax: n = %d, ib = %d, im = %d\n",n,ib,im);
            flag = 1;
        }
     }
     n0  *= 4;                    // increase n
     kl   = 4;                    // for n > 1, 3 steps of increase in n
  }
  if(flag==0) printf(" All n tests pass\n");
  return 0;
}
#define NS 12
int isamax(int n, float *x)
{
  float rbig,*xp;
  int i,ii,nres,nsegs,ibig,irbig;
  vector float V0,V1,V6;
  vector bool int V3;
  vector float V2 = (vector float) (0.0,1.0,2.0,3.0);
  vector float V7 = (vector float) (0.0,1.0,2.0,3.0);
  const vector float incr_4 = (vector float) (4.0,4.0,4.0,4.0);
  const vector float minus0 = (vector float) (-0.0,-0.0,-0.0,-0.0);
  float big;
  float xbig[4]  __attribute__((aligned(16)));
  float indx[4]  __attribute__((aligned(16)));
// n < NS done in scalar mode
  if(n < NS){
     ibig = 0;
     rbig = 0.0;
     for(i=0;i<n;i++){
        if(fabs(x[i]) > rbig){
           rbig = fabs(x[i]);
           ibig = i;
        }
     }
     return(ibig);
  }
// n >= NS case done with altivec 
  nsegs = (n >> 2) - 1;
  nres  = n - ((nsegs+1) << 2);    // nres = n mod 4
  V2 = vec_add(V2,incr_4);         // increment next index
  xp = x;
  V0 = vec_ld(0,xp); xp += 4;      // first four 
  V1 = vec_ld(0,xp); xp += 4;      // next four
  V0 = vec_abs(V0);                // absolute value of first four
  for(i=0;i<nsegs;i++){
     V1 = vec_abs(V1);             // take absolute value fo next segment
     V3 = vec_cmpgt(V1,V0);        // compare accumulated 4 to next 4
     V0 = vec_sel(V0,V1,V3);       // select new or old accumulation
     V7 = vec_sel(V7,V2,V3);       // select new index or old
     V1 = vec_ld(0,xp); xp += 4;   // bottom load next 4
     V2 = vec_add(V2,incr_4);
  }
  V1 = vec_ld(0,xp); xp += 4;  // bottom load next four
  V3 = vec_cmpgt(V1,V0);      // compare accumulated to last 4
  V0 = vec_sel(V0,V1,V3);     // select accumulation to last 4
  V7 = vec_sel(V7,V2,V3);     // select index of accum. to last 4
// Now finish up: segment maxima are in V0, indices in V7
  vec_st(V0,0,xbig);
  vec_st(V7,0,indx);
  ii   = ((n >> 2) << 2);
  big  = 0.0;
  ibig = 0.0;
  for(i=0;i<nres;i++){
     if(fabs(x[ii]) > big){
        big  = fabs(x[ii]);
        ibig = ii;
     }
     ii++;
  }
  for(i=0;i<4;i++){
     if(xbig[i] > big){
        big  = xbig[i];
        ibig = (int) indx[i];
     }
  }
  return(ibig);
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

