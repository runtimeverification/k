#include <stdlib.h>
#include <stdio.h>

static int Partition(int A[], int l, int r, int pv)
  {
    int i = l;
    int j = r-1;
    // swap A[l] and A[j]
    int tmp = A[l];
    A[l] = A[j];
    A[j] = tmp;
 
    while (i < j)
    {
      if (A[i] <= pv) {
        i++;
      } else if (pv <= A[j-1]) {
        j--;
      } else {
        // swap A[j-1] and A[i]
        tmp = A[i];
        A[i] = A[j-1];
        A[j-1] = tmp;
        i++;
        j--;
      }
    }
 
    return i;
  }
  
int main()
{
  int a[30];
  int size = 30;
  
  while(size>0)
  {
    a[size-1] = size;
    size--;
  }
  
  Partition(a,3,7,10);
  
  return 0;
}

