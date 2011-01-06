#include <stdlib.h>
#include <stdio.h>

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

int main()
{
  int a[30];
  int size = 0;
  
  while(size<30)
  {
    a[size] = size;
    size++;
  }
  print(a,30);
  swap(a,3,20,30);
  print(a,30);
  return 0;
}

//as seen on spec# examples

