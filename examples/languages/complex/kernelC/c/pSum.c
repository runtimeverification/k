    #include<stdio.h>
    #include<stdlib.h>
    int main() {
         int n = 1000 ;
	 int s = 0 ;
         int i = n ;
         while (!(i <= 0)) {
           s = s + i ;
           i = i - 1 ;
         } 
         printf("%d;",s);
    }

