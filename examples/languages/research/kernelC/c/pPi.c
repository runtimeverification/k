#include <stdio.h>
#include <stdlib.h>

int nrand(int n) {
  return random()%n;
}

int find(int* a, int n, int x, int k) {
  int i = 0; int p;
  while (i++<k) {
    if (a[p=nrand(k)]==x) return p;
  }
  return -1;
}

int main() {
  int s; int n;
  scanf("%d",&s);
  srandom(s);
  scanf("%d",&n);
  int i=0;
  unsigned int x; unsigned int y; int k=0;
  while (i++<n) {
    x = 5000 - nrand(10000);
    y = 5000 - nrand(10000);
    if (x*x + y*y < 25000000) k++; 
  }
  printf("%d;", k);
  return 0;
}


