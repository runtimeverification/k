/*************************    Program 3.2    ****************************/
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
#define NMAX 60
#define MMAX   14
#define g1(x1,x2,t) (x2)
#define g2(x1,x2,t) (-q*x2-sin(x1)+b*cos(w*t))
const double q=0.5,b=0.9,w=2.0/3;

main()
/* Main Program for a driven pendulum under damping solved with
   the fourth-order Runge-Kutta algorithm.  Parameters: Q, B,
   and W (omega_0).  Copyright (c) Tao Pang 1997. */
{
int i,n,m,l,np;
double pi,h,t,dk11,dk21,dk12,dk22,dk13,dk23,dk14,dk24;
double y1,y2;
double y[2][NMAX];

n  = NMAX;
m  = MMAX;
l  = 10;
pi = 4*atan(1);
h  = 3*pi/m;

y[0][0] = 0;
y[1][0] = 2;

/* Using the Runge-Kutta algorithm to integrate the equation */

for (i = 0;  i < n-1; ++i)
  {
  t = h*(i+1);
  y1 = y[0][i];
  y2 = y[1][i];
  dk11 = h*g1(y1,y2,t);
  dk21 = h*g2(y1,y2,t);
  dk12 = h*g1((y1+dk11/2),(y2+dk21/2),(t+h/2));
  dk22 = h*g2((y1+dk11/2),(y2+dk21/2),(t+h/2));
  dk13 = h*g1((y1+dk12/2),(y2+dk22/2),(t+h/2));
  dk23 = h*g2((y1+dk12/2),(y2+dk22/2),(t+h/2));
  dk14 = h*g1((y1+dk13),(y2+dk23),(t+h));
  dk24 = h*g2((y1+dk13),(y2+dk23),(t+h));
  y[0][i+1] = y[0][i]+(dk11+2*(dk12+dk13)+dk14)/6;
  y[1][i+1] = y[1][i]+(dk21+2*(dk22+dk23)+dk24)/6;

/* Bring theta back to the region [-pi,pi] */
 
  np = y[0][i+1]/(2*pi)+0.5;
  y[0][i+1] = y[0][i+1]-2*pi*np;
  if ((i == 0) || ((i+1)%l == 0))
    printf("%d %d\n", (int)((y[0][i])*10000), (int)((y[1][i])*10000));
  }
  return 0;
}
