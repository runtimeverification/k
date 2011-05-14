 int * string2() {
    int * p =  (int *)malloc(100*sizeof(int));
    int i = 0 ;
    while (i <= 98) {
      p[i] = i + 5 ;
      i = i + 1 ;
    }
    p[99] = 0 ;
    return p;
}

