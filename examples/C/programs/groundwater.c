/*************************    Program 6.3    ****************************/
/*                                                                      */
/************************************************************************/
/* Please Note:                                                         */
/*                                                                      */
/* (1) This computer program is written by Tao Pang in conjunction with */
/*     his book, "An Introduction to Computational Physics," published  */
/*     by Cambridge University Press in 1997.                           */
/*                                                                      */
/* (2) No warranties, express or implied, are made for this program.    */
/*                                                                      */
/************************************************************************/

#include <stdio.h>
#include <math.h>
// #define NXMX  101
// #define NYMX   51
// #define ITMX    5
#define NXMX  6
#define NYMX   3
#define ITMX    2

int main()
/* This program solves the groundwater dynamics problem in the
   rectangular geometry through the relaxation method.
   Copyright (c) Tao Pang 1997. */
{
int i,j,nx,ny,istep;
double pi,a0,b0,h0,ch,sx,sy,hx,hy,p,x,y;
double phi[NXMX][NYMX],ck[NXMX][NYMX],sn[NXMX][NYMX];
void rx2d();

nx = NXMX;
ny = NYMX;
pi = 4*atan(1);
a0 = 1;
b0 = -0.04;
h0 = 200;
ch = -20;
sx = 1000;
sy = 500;
hx = sx/(nx-1);
hy = sy/(ny-1);
p  = 0.5;

/* Set up boundary conditions and initial guess of the solution */

for (i = 0; i < nx; ++i)
  {
  x = i*hx;
  for (j = 0; j < ny; ++j)
    {
    y = j*hy;
    ck[i][j]  = a0+b0*y;
    phi[i][j] = h0+ch*cos(pi*x/sx)*y/sy; 
    sn[i][j]  = 0;
    }
  }
for (istep = 0; istep < ITMX; ++istep)
  {
/* Ensure the boundary conditions by the 4-point formula */

  for (j = 0; j < ny; ++j)
    {
    phi[0][j]  =(4*phi[1][j]-phi[2][j])/3;
    phi[nx-1][j]  =(4*phi[nx-2][j]-phi[nx-3][j])/3;
    }
  rx2d (phi,ck,sn,nx,ny,p,hx,hy);
  }

for (i = 0; i < nx; ++i)
  {
  x = i*hx;
  for (j = 0; j < ny; ++j)
    {
    y = j*hy;
    printf("%d %d %d\n", (int)(x*10), (int)(y*10), (int)(phi[i][j])*10);
    }
  }
  return 0;
}

void rx2d (fn,dn,s,nx,ny,p,hx,hy)
/* Subroutine performing one iteration of the relaxation for the
   two-dimensional Poisson equation.  Copyright (c) Tao Pang 1997. */

int nx,ny;
double p,hx,hy;
double fn[NXMX][NYMX],dn[NXMX][NYMX],s[NXMX][NYMX];
{
int i,j;
double hx2,a,b,q,cip,cim,cjp,cjm;

hx2 = hx*hx;
a   = hx2/(hy*hy);
b   = 1/(4*(1+a));
q   = 1-p;

for (i = 1; i < nx-1; ++i)
  {
  for (j = 1; j < ny-1; ++j)
    {
    cip = b*(dn[i+1][j]/dn[i][j]+1);
    cim = b*(dn[i-1][j]/dn[i][j]+1);
    cjp = a*b*(dn[i][j+1]/dn[i][j]+1);
    cjm = a*b*(dn[i][j-1]/dn[i][j]+1);
    fn[i][j] = q*fn[i][j]+p*(cip*fn[i+1][j]+cim*fn[i-1][j]
              +cjp*fn[i][j+1]+cjm*fn[i][j-1]+hx2*s[i][j]);
    }
  }
}
