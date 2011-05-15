 int reverse(int *p) {
  int * x ; int * y ;
 if (p) {
  x = *(p + 1) ;
  *(p + 1) = NULL ;
  while (x) {
   y = *(x + 1);
   *(x + 1) = p ;
   p = x ;
   x = y ;
  }
 }
 return p ;
}

