#include<stdio.h>
#include<stdlib.h>
#include<array.h>
int main() {
  int * x = arrRead(); arrPrint(x);
  int * y = arrRead(); arrPrint(y);
  arrCpy(x,y);
  arrPrint(x); arrPrint(y);
  return 0;
}

