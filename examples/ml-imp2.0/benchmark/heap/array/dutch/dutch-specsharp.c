#include <stdlib.h>
#include <stdio.h>
#include <time.h>

void swap(int a[], int i, int j, int size)
{
  int tmp;
  tmp = a[i];
  a[i] = a[j];
  a[j] = tmp;
}

void print(int a[], int size)
{
  while(size>0)
  {
    printf("%d ",a[size-1]);
    size--;
  }
  printf("\n\n");
}

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
  
static void Test(int l)
{
  int A[l];
  int i=0;
  while(i < l)
  {
    A[i] = rand() % 3;
    i++;
  }
  print(A,l);
   
  int p = Partition(A, 0, l, A[0]);
  print(A,l);

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
  
  Test(10);
  
  return 0;
}

