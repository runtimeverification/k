void freeList(int * p) {
int * q;
 while (p) {
  q = * (p + 1) ;
  free(p) ;
  p = q ;
 }
}

