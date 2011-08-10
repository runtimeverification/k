load kernelc-syntax
kmod KERNELC-MONTE-CARLO is including KERNELC-SYNTAX 
macro pMonteCarlo =

#include <stdio.h>
#include <stdlib.h>

int nrand(int n) {
  return rand()%n;
}

int find(int* a, int n, int x, int k) {
  int i = 0; int p;
  while (i++<k) {
    if (a[p=nrand(n)]==x) return p;
  }
  return -1;
}

int main() {
  int s; int n; int k; int x;
  scanf("%d",&s);
  srand(s);
  scanf("%d",&n);
  scanf("%d",&k);
  scanf("%d",&x);
  int *a = (int*)malloc(n*sizeof(int));
  int i=0;
  while (i<n) { scanf("%d",a+i++); }
  if (find(a,n,x,k)!=-1)  { printf("%d;", 1); } else { printf("%d;", 0); }
  return 0;
}



syntax Pgm ::= pMonteCarlo 
syntax #Id ::=  a | n | s | x | k | i | p | nrand | find 
endkm

