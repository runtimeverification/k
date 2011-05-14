int * string() {
    int * p =  (int *)malloc(5*sizeof(int));
    p[0] = 1; p[1] = 2 ; p[2] = 3 ; p[3] = 4 ; p[4] = 0 ;
    return p;
}

