void print(int *a) {
  int * p;
 p = a ;
 while (p) {
  printf("%d;",* p);
  p = * (p + 1) ;
 }
}
 

