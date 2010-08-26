/* Updated 10/24/2001. */

/*************************    Program 4.3    ****************************/
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
#define NMAX 3

main()
/* An example of solving linear equation set a[][] x[] = b[]
   with the partial-pivoting Gaussian elimination scheme.  The
   numerical values are for the Wheatstone bridge example discussed
   in Section 4.1 in the book with all resistances being 100 ohms
   and the voltage 200 volts.  Copyright (c) Tao Pang 2001. */

{
  double x[3], b[3]={200,0,0};
  double a[3][3]={{100,100,100},{-100,300,-100},{-100,-100,300}};   
  int i, n=3, indx[3];
  void legs();

  legs (a,n,b,x,indx);

  for (i=0; i<n; i++)
  {
    printf("%d\n", (int)((x[i])*10000));
  }
}

void legs (a,n,b,x,indx)

/* Function to solve the equation a[][] x[] = b[] with the
   partial-pivoting Gaussian elimination scheme.
   Copyright (c) Tao Pang 2001. */

int n;
int indx[];
double b[],x[];
double a[NMAX][NMAX];
{
  int i,j;
  void elgs();

  elgs (a,n,indx);

  for(i = 0; i < n-1; ++i)
  {
    for(j = i+1; j < n; ++j)
    {
      b[indx[j]] = b[indx[j]]-a[indx[j]][i]*b[indx[i]];
    }
  }

  x[n-1] = b[indx[n-1]]/a[indx[n-1]][n-1];
  for (i = n-2; i>=0; i--)
  {
    x[i] = b[indx[i]];
    for (j = i+1; j < n; ++j)
    {
      x[i] = x[i]-a[indx[i]][j]*x[j];
    }
    x[i] = x[i]/a[indx[i]][i];
  }
}

void elgs (a,n,indx)

/* Function to perform the partial pivoting Gaussian elimination.
   a[][] is the original matrix in the input and transformed
   matrix plus the pivoting element ratios below the diagonal
   in the output.  indx[] records the pivoting order.
   Copyright (c) Tao Pang 2001. */

int n;
int indx[];
double a[NMAX][NMAX];
{
  int i, j, k, itmp;
  double c1, pi, pi1, pj;
  double c[NMAX];

  if (n > NMAX)
  {
    printf("The matrix dimension is too large.\n");
    exit(1);
  }

/* Initialize the index */

  for (i = 0; i < n; ++i)
  {
    indx[i] = i;
  }

/* Find the rescaling factors, one from each row */
 
  for (i = 0; i < n; ++i)
  {
    c1 = 0;
    for (j = 0; j < n; ++j)
    {
      if (fabs(a[i][j]) > c1) c1 = fabs(a[i][j]);
    }
    c[i] = c1;
  }

/* Search the pivoting (largest) element from each column */ 

  for (j = 0; j < n-1; ++j)
  {
    pi1 = 0;
    for (i = j; i < n; ++i)
    {
      pi = fabs(a[indx[i]][j])/c[indx[i]];
      if (pi > pi1)
      {
        pi1 = pi;
        k = i;
      }
    }

/* Interchange the rows via indx[] to record pivoting order */

    itmp = indx[j];
    indx[j] = indx[k];
    indx[k] = itmp;
    for (i = j+1; i < n; ++i)
    {
      pj = a[indx[i]][j]/a[indx[j]][j];

/* Record pivoting ratios below the diagonal */

      a[indx[i]][j] = pj;

/* Modify other elements accordingly */

      for (k = j+1; k < n; ++k)
      {
        a[indx[i]][k] = a[indx[i]][k]-pj*a[indx[j]][k];
      }
    }
  }
}
