#include <stdlib.h>
#include <stdio.h>
 
int Coincidence(int f[], int g[], int fLength, int gLength)
{ 
  int ct = 0;
  int m = 0;
  int n = 0;

  while( (m < fLength) || (n < gLength))
  { if ((n == gLength) ||(m < fLength && f[m] < g[n]))
    {
      m++;
    }
    else if((m == fLength) || ( n < gLength && g[n] < f[m]))
         {   n++;
         }
        else
          {//(g[n] == f[m]);
           ct++;
           m++;
           n++;
          }
 
  }
return ct;
}

int main()
{
  int f[] = {2,4};
  int g[] = {1,4,6};
  printf("Coincidence: %d\n",Coincidence(f,g,2,3));
  return 0;
}
