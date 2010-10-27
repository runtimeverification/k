
#include "bits.h"


int main(int argc, char ** argv)
{
  int68 n1;
  uint68 n2;
  uint63 t1;
  uint3 t2;
  uint128 t3;
  unsigned long long t4;

  printf("concat(i25,i39)=");
  t4 = bit_concat((uint25) -1, (uint39)-1);
  printBits(t4);
  printf("\n");
  
  n1 = -1;
  n2 = -1;
  printf("n1 = ");
  printBits(n1);
  printf("\nn2 = ");
  printBits(n2);
  printf("\n");
  printf("concat(i68 n2, i60 -1)=");
  t3 = bit_concat(n2, (uint60)-1);
  printBits(t3);
  printf("\n");
  
  return 0;
}
