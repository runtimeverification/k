#include <stdio.h>


int main() {
  int n;
  int i;
  int flag;

  flag = 1;
  i = 2;
  n=78;
  
  while ((i < (n/2)) && (flag == 1))
  {
    if ((n % i) == 0) flag = 0;
    else i++;
  }
   
  if (flag)    printf("%d is prime\n", n);
  else    printf("%d has %d as a factor\n", n, i);
  return 0;
}
