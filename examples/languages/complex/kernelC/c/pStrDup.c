int * strDup(int * a) {
    int * p = (int *)malloc((strLen(a)+1)*sizeof(int)) ;
    strCpy(p,a);
    return p;
  }

