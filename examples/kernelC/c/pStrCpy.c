void strCpy(int * a, int * b) {
   while (* b) {
     * a = * b ;
     b = b + 1 ;
     a = a + 1 ;
   }
   * a = 0 ;
}

