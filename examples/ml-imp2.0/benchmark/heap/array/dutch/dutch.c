#include <stdlib.h>
#include <stdio.h>

// modulo 3 classes: 0 = blue, 1 = white, 2 = red;

void monochromize(int a[], int start, int end)
{
  int b = start; //blue
  int i = start; // iterator
  int r = end; // red
  int tmp;
  
  while (i < r)
  {
    if (a[i] == 0)
    {
      tmp = a[b];
      a[b] = a[i];
      a[i] = tmp;
      b++;
      i++;
    }
    else 
    if (a[i] == 2)
    {
      r--;
      tmp = a[r];
      a[r] = a[i];
      a[i] = tmp;
    }
    else i++;
  }
}

void print(int a[], int start, int end)
{
  while(start<=end)
  {
    printf("%d ",a[start]);
    start++;
  }
  printf("\n");
}

int main()
{
  int a[30];
  int aux=0;
  
  while(aux<30)
  {
    a[aux] = (aux % 3);
    aux++;
  }
  print(a,0,29);
  monochromize(a,0,29);
  print(a,0,29);
  return 0;
}
