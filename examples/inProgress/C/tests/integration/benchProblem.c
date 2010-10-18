/*************************    Program 6.1    ****************************/
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
// #define NMAX 99
// #define MMAX   500
#define NMAX 20
#define MMAX   75

int main()
/* This program solves the problem of a person sitting on a
   bench as described in the text.  Copyright (c) Tao Pang 1997. */
{
int n,i;
double xl,h,h2,y0,x0,xd,rho,g,d,e,e0,f0;
double b[NMAX],x[NMAX],y[NMAX],w[NMAX],u[NMAX];

n = NMAX;
xl = 3;
h = xl/(n+1);
h2 = h*h;
y0 = 1e9*pow(0.03,3)*0.2/3;
x0 = 0.25;
rho = 3;
g = 9.8;
f0 = 200;
d =  2;
e = -1;
e0  = 1.0/exp(1.0);

/* Find elements in L and U */

w[0] = d;
u[0] = e/d;
for (i = 1; i < n; ++i)
  {
  w[i] = d-e*u[i-1];
  u[i] = e/w[i];
  }

/* Assign the array B */

for (i = 0; i < n; ++i)
  {
  xd   =  h*(i+1);
  b[i] = -h2*rho*g;
  if (fabs(xd-xl/2) < x0)
    b[i] = b[i]-h2*f0*(exp(-pow((xd-xl/2)/x0,2))-e0);
  b[i] = b[i]/y0;
  }

/* Find the solution of the curvature */

y[0] = b[0]/w[0];
for (i = 1; i < n; ++i)
  {
  y[i] = (b[i]+y[i-1])/w[i];
  }
x[n-1] = y[n-1];
for (i = n-2; i >= 0; i = i-1)
  {
  x[i] = y[i]-u[i]*x[i+1];
  }
for (i = 0; i < n; ++i)
  {
  printf("%d %d\n", (int)((h*(i+1))*1000),(int)((100*x[i])*1000));
  }
  return 0;
}
