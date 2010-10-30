#include "fsl-header.h"
/* REPRODUCED:RUN:SIGNAL MACHINE:sparc OPTIONS: */
void f(int n)
{
int i;
double v[n];
for(i=0;i<n;i++)
v[i]=0;
}
main()
{
f(100);
exit(0);
}
