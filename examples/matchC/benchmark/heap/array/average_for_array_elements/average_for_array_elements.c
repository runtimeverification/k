#include <stdlib.h>
#include <stdio.h>

void initialize(int a[], int size)
{
  while(size > 0)
  {
    a[size-1] = size;
    size--;
  }
}

int average(int a[], int start, int end)
{
	int sum;
  int size;
  int average;
	sum = 0;
  size = 0;
  
  while((start + size)<=end)
  {
    sum = sum + a[start+size];
    size++;
  }

  if(size>0) return sum/size;
  else return -1;
}

int main()
{
  int a[30];
  int aux = 30;
  int s;
  
  initialize(a,30);
  
  s = average(a,0,29);
  
  printf("The average for the elements of the array is: %d\n",s);
  
  return 0;
}

