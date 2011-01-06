#include <stdlib.h>
#include <stdio.h>

static int BLS(int a[], int key, int Length)
{
  int n =0;
  while(n < Length && a[n] != key) n++;
  if (n == Length)
  return -1;
  else return n;
}

static int BLS2(int a[], int key, int Length)
/*Leaving out 0<result as a conjunct of postcondition 1 leads to    an unsatisfied postcondition: ensures  result < Length ==> a    [result] == key; */   
{
  int n=0;
/* Rather than placing the (a[n] != key) condition in the loop       guard, place an if statement within the loop */

  while(n < Length)
  {
    if (a[n] == key)
    { 
      return n;
      break;
    }
    n++;
  }
 return -1;
}

int main()
{
  int a[] = { 4, 0, 12, 64, -10, 20 };
  int s = BLS(a, 12,5);
  int s1 = BLS2(a, 12,5);
  printf("The result is %d\n", s);
  printf("The result is %d\n", s1);
}
