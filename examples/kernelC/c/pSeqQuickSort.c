#include<stdio.h>
#include<stdlib.h>
#include<qsort.h>
#include<array.h>

int main() {
  int * a = arrRead();
  quickSort(a,a+arrLen(a));
  arrPrint(a);
  free(a);
  return 0;
}

