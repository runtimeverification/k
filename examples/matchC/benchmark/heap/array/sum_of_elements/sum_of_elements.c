#include <stdlib.h>
#include <stdio.h>

int sum(int a[], int size)
{
	int s;
	s = 0;
	while(size>0)
	{
		s = s + a[size-1];
		size--;
	}
	return s;
}

int main()
{
  int a[30];
  int aux = 30;
  int s;
  
  while(aux > 0)
  {
    a[aux-1] = aux;
    aux--;
  }
  
  s = sum(a,30);
  
  printf("The sum of elements of the array is: %d\n",s);
  
  return 0;
}

