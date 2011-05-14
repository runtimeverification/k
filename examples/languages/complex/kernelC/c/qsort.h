void quickSort(int *b,int *e) {
  int t ;
  if (! (e <= b + 1)) {
    int p = *b;
    int *l = b+1;
    int *r = e;
    while  (l+1<= r) {
      if (*l <= p) {
        l = l + 1;
      } else { 
        r = r - 1;
        t=*l;*l=*r;*r=t;
      }
    }
    l = l - 1;
    t=*l;*l=*b;*b=t;
    quickSort(b,l); 
    quickSort(r,e);
  }
}

