#include <stdio.h>
    int f() {
       int n;
       n = -1;
       return n;
    }

    int main() {
       int i = 1;
       if (i > 0)
          while (i > 0) { i = i+1+f(); }
       else
          i = 0;
    }

