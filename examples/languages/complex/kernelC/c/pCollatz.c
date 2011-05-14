    #include<stdio.h>
    #include<stdlib.h>
    int main() {
         int limit = 10 ;
         int steps = 0 ; int nr = 2 ;
         int n; int d; int nn;
         while (nr <= limit) {
           n = nr ; nr = nr + 1 ;
           while (!(n <= 1)) {
             steps = steps + 1 ;
	     d = 0 ;
             nn = 2 ;
             while (nn <= n) {
               d = d + 1 ;
               nn = nn + 2 ;
             }
             if (nn <= (n + 1)) n = n + n + n + 1 ; else n = d ;
           }
         } 
         printf("%d;",steps);
  } 

