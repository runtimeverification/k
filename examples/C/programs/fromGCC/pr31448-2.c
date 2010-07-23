/* PR middle-end/31448, this used to ICE during expand because
   reduce_to_bit_field_precision was not ready to handle constants. */
#include <stdio.h>
typedef struct _st {
    long int iIndex : 24;
    long int iIndex1 : 24;
} st;
st *next;
void f(void)
{
    int nIndx;
    const static long int constreg[] = { 0xFEFEFEFE,};
    nIndx = 0;
    next->iIndex = constreg[nIndx];
    next->iIndex1 = constreg[nIndx];
	printf("%d\n", constreg[0]);
	printf("%d\n", (long int)next->iIndex);  
	printf("%d\n", (long int)0xFFFEFEFE);  
	
}
int main(void)
{
  st a;
  next = &a;
  f();
  if (next->iIndex != 0xFFFEFEFE)
    __builtin_abort ();
  if (next->iIndex1 != 0xFFFEFEFE)
    __builtin_abort ();
  return 0;
}

