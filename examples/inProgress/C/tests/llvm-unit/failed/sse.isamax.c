#include <stdio.h>
#include <math.h>
#include <float.h>
#include "xmmintrin.h"
#define N 20
int main()
{
/* 
  SSE unit step isamax with alignment code. From Section
  3.5.7 of Petersen and Arbenz "Intro. to Parallel Computing,"
  Oxford Univ. Press, 2004.

                             wpp 31/7/2002 
*/
  float x[N];
  int i,im;
  int isamax0(int,float *);
  for(i=0;i<N;i++){
     x[i] = -2.0 + (float) i;
  }
  x[7] =33.0;
  im = isamax0(N,x);
  printf(" maximum index = %d\n",im);
  printf(" maximum value = %e\n",x[im]);
  return 0;
}
#define NS 12
int isamax0(int n, float *x)
{
  float bbig,ebig,bres,*xp;
  int eres,i,ibbig,iebig,align,nsegs,mb,nn;
  __m128 offset4,V0,V1,V2,V3,V6,V7;
  float xbig[8] __attribute__ ((aligned (16)));
  float indx[8] __attribute__ ((aligned (16)));
// n < NS done in scalar mode
  if(n < NS){
     iebig = 0;
     bbig  = 0.0;
     for(i=0;i<n;i++){
        if(fabs(x[i]) > bbig){
           bbig  = fabs(x[i]);
           iebig = i;
        }
     }
     return(iebig);
  }
// n >= NS case done in SSE mode
  V7      = _mm_set_ps(3.0,2.0,1.0,0.0);
  V2      = _mm_set_ps(3.0,2.0,1.0,0.0);
  V6      = _mm_set_ps1(-0.0);
  offset4 = _mm_set_ps1(4.0);
  align = ((unsigned int) x >> 2) & 0x03;
  if(align == 1){        // bres = 3 case
     bbig = fabsf(x[0]); ibbig = 0; 
     bres = 3.0; nn = n - 3;
     for(i=1;i<3;i++){
        if(fabsf(x[i]) > bbig){
           bbig = fabsf(x[i]); ibbig = i;
        }
     }
  } else if(align == 2){    // bres = 2 case
     bbig = fabsf(x[0]); ibbig = 0;
     bres = 2.0; nn = n - 2;
     if(fabsf(x[1]) > bbig){
        bbig  = fabsf(x[1]); ibbig = 1;
     }
  } else if(align == 3){    // bres = 1 case
     bbig = fabsf(x[0]); ibbig = 0;
     bres = 1.0; nn = n - 1;
  } else {                  // bres = 0 case
     bbig = 0.0; ibbig = 0; nn = n;
     bres = 0.0;
  }
  xp = x + (int) bres;
  nsegs = (nn >> 2) - 2;
  eres  = nn - 4*(nsegs+2); 
  V0 = _mm_load_ps(xp); xp += 4;   // first four in 4/time seq.
  V1 = _mm_load_ps(xp); xp += 4;   // next four in 4/time seq.
  V0 = _mm_andnot_ps(V6,V0);       // take absolute value
  for(i=0;i<nsegs;i++){
     V1 = _mm_andnot_ps(V6,V1);    // take absolute value
     V3 = _mm_cmpnle_ps(V1,V0);    // compare old max of 4 to new
     mb = _mm_movemask_ps(V3);     // any of 4 bigger?
     V2 = _mm_add_ps(V2,offset4);  // add offset
     if(mb > 0){
        V0 = _mm_max_ps(V0,V1);
        V3 = _mm_and_ps(V2,V3);
        V7 = _mm_max_ps(V7,V3);
     }
     V1 = _mm_load_ps(xp); xp += 4;  // bottom load next four
  }
// finish up the last segment of 4
  V1 = _mm_andnot_ps(V6,V1);    // take absolute value
  V3 = _mm_cmpnle_ps(V1,V0);    // compare old max of 4 to new
  mb = _mm_movemask_ps(V3);     // any of 4 bigger?
  V2 = _mm_add_ps(V2,offset4);  // add offset
  if(mb > 0){
     V0 = _mm_max_ps(V0,V1);
     V3 = _mm_and_ps(V2,V3);
     V7 = _mm_max_ps(V7,V3);
  }
// Now finish up: segment maxima are in V0, indices in V7
  _mm_store_ps(xbig,V0);
  _mm_store_ps(indx,V7);
  if(eres>0){
    for(i=0;i<eres;i++){
       xbig[4+i] = fabsf(*(xp++));
       indx[4+i] = (float) (nn+i);
    }
  }
  ebig  = bbig; 
  iebig = ibbig; 
  for(i=0;i<4+eres;i++){
     if(xbig[i] > ebig){
        ebig = xbig[i];
        iebig = (int) (indx[i]+bres);
     }
  }
  return(iebig);
}
#undef NS
