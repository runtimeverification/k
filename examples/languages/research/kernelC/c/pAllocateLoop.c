int allocateLoop(int a,int * p) {
 int n = 0 ;
 int * q ;
 while (n != a) {
  q = (int *)malloc(2 * sizeof(int)) ;
  * q = n ;
  * (q + 1) = p ;
  p = q ;
  n = n + 1 ;
 }
 return p ;
}


